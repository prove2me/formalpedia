-- Prove2me | solution 1 for MmSChores.RoundRobin.mms_le_dmin
-- status  : ACCEPTED   (prove)
-- author  : @queelius
-- created : 2026-10-26T06:43:21.821721+00:00
-- url     : https://prove2.me/submissions/4cba1cfb-e160-4364-94c5-c245e3c43a00

import Definitions.Def_LittleCharity_EFX_Setting
import Definitions.Def_MmSChores_RoundRobin_TightInstance
import Definitions.Def_LittleCharity_MMS_Setting
import Definitions.Def_MmSChores_RoundRobin_Setting
import Init
import Mathlib





section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

theorem partition_sum {N m : ℕ} (d : Fin N → Fin m → ℝ) (i : Fin N)
    (f : Fin m → Fin N) :
    ∑ j, bval d i (univ.filter (fun g => f g = j)) = bval d i univ := by
  classical
  simp only [bval, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro g hg
  simp

theorem mms_average {N m : ℕ} (hN : 0 < N) (d : Fin N → Fin m → ℝ) (i : Fin N) :
    LittleCharity.MMS.mms (bval d i) N univ ≤ (1 / (N : ℝ)) * bval d i univ := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  unfold LittleCharity.MMS.mms
  apply ciSup_le
  intro f
  have h (j : Fin N) : (⨅ j : Fin N, bval d i (univ.filter (fun g => f g = j))) ≤
      bval d i (univ.filter (fun g => f g = j)) :=
    ciInf_le (Set.finite_range _).bddBelow j
  have hh:=sum_le_sum (s:=univ) (fun j _ => h j)
  rw [partition_sum d i f] at hh
  simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at hh
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  rw [one_div, mul_comm, ←div_eq_mul_inv]
  apply (le_div_iff₀ hn).mpr
  simpa only [mul_comm] using hh

theorem mms_item {N m : ℕ} (hN : 0 < N) (d : Fin N → Fin m → ℝ) (i : Fin N)
    (hd : ∀ j, d i j ≤ 0) (g : Fin m) :
    LittleCharity.MMS.mms (bval d i) N univ ≤ d i g := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  unfold LittleCharity.MMS.mms
  apply ciSup_le
  intro f
  apply (ciInf_le (Set.finite_range _).bddBelow (f g)).trans
  unfold bval
  have hs : {g} ⊆ univ.filter (fun x => f x = f g) := by simp
  have hh:=sum_le_sum_of_subset_of_nonneg (f := fun x => -d i x) hs (fun x _ _ => neg_nonneg.mpr (hd x))
  simpa only [sum_neg_distrib, neg_le_neg_iff, sum_singleton] using hh

theorem mms_minimum {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (i : Fin N) (hd : ∀ j, d i j ≤ 0) :
    LittleCharity.MMS.mms (bval d i) N univ ≤ univ.inf' hm (d i) := by
  apply le_inf'
  intro g hg
  exact mms_item hN d i hd g
end Queelius.Chores

end

section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

def owner {N m : ℕ} (hN : 0 < N) (σ : Fin m ≃ Fin m) (g : Fin m) : Fin N :=
  ⟨(σ.symm g).val % N, Nat.mod_lt _ hN⟩

theorem rr_membership {N m : ℕ} (hN : 0 < N) (σ : Fin m ≃ Fin m) (i : Fin N) (g : Fin m) :
    g ∈ rrBundle σ i ↔ owner hN σ g = i := by
  simp [rrBundle, owner, Fin.ext_iff]

theorem rr_disjoint {N m : ℕ} (hN : 0 < N) (σ : Fin m ≃ Fin m) :
    Pairwise (fun i j : Fin N => Disjoint (rrBundle σ i) (rrBundle σ j)) := by
  intro i j hij
  apply disjoint_left.mpr
  intro g hi hj
  have hi := (rr_membership hN σ i g).mp hi
  have hj := (rr_membership hN σ j g).mp hj
  exact hij (hi.symm.trans hj)

theorem rr_cover {N m : ℕ} (hN : 0 < N) (σ : Fin m ≃ Fin m) :
    univ.biUnion (rrBundle σ : Fin N → Finset (Fin m)) = univ := by
  ext g
  simp only [mem_biUnion, mem_univ, true_and, iff_true]
  exact ⟨owner hN σ g, (rr_membership hN σ _ g).mpr rfl⟩

def picks {N m : ℕ} (i : Fin N) : Finset (Fin m) := univ.filter (fun t => t.val % N = i.val)

theorem bundle_picks {N m : ℕ} (d : Fin N → Fin m → ℝ) (σ : Fin m ≃ Fin m) (i j : Fin N) :
    bval d i (rrBundle σ j) = ∑ t ∈ picks (m:=m) j, d i (σ t) := by
  classical
  apply sum_equiv σ.symm
  · intro g
    simp [rrBundle,picks]
  · intro g hg
    simp

theorem negative_sum_subset {α : Type*} [DecidableEq α] {s t : Finset α}
    (f : α → ℝ) (h : s ⊆ t) (hf : ∀ a ∈ t, f a ≤ 0) :
    ∑ a ∈ t, f a ≤ ∑ a ∈ s, f a :=
  sum_le_sum_of_subset_of_nonneg (N := OrderDual ℝ) h (fun a ha _ => hf a ha)

theorem same_residue_gap {N a b : ℕ} (hN : 0 < N) (hab : a < b) (hmod : a % N = b % N) :
    a + N ≤ b := by
  have had := Nat.mod_add_div a N
  have hbd := Nat.mod_add_div b N
  have hdivle := Nat.div_le_div_right hab.le (c:=N)
  have hdiv : a/N < b/N := by
    by_contra h
    have he : a/N=b/N := by omega
    rw [he,hmod] at had
    omega
  have hmul := Nat.mul_le_mul_left N (Nat.succ_le_of_lt hdiv)
  rw [Nat.mul_succ] at hmul
  omega
end Queelius.Chores

end

section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

theorem greedy_permutation {m : ℕ} (w : Fin m → Fin m → ℝ) :
    ∃ σ : Fin m ≃ Fin m, ∀ t u : Fin m, t ≤ u → w t (σ u) ≤ w t (σ t) := by
  classical
  let score (σ : Fin m ≃ Fin m) : Lex (Fin m → ℝ) := toLex (fun t => w t (σ t))
  obtain ⟨σ,hσ,hmax⟩:=univ.exists_max_image score (by exact univ_nonempty)
  refine ⟨σ,?_⟩
  intro t u htu
  by_contra h
  let τ := (Equiv.swap t u).trans σ
  have hlex : score σ < score τ := by
    refine ⟨t,?_,?_⟩
    · intro k hkt
      dsimp [score,τ]
      rw [Equiv.swap_apply_of_ne_of_ne hkt.ne (hkt.trans_le htu).ne]
    · simpa [score,τ] using lt_of_not_ge h
  exact (not_lt_of_ge (hmax τ (mem_univ _))) hlex

theorem run_exists (N m : ℕ) (d : Fin N → Fin m → ℝ) :
    ∃ σ : Fin m ≃ Fin m, IsRoundRobinRun d σ := by
  classical
  by_cases hn : N=0
  · subst N
    refine ⟨Equiv.refl _,?_⟩
    intro i
    exact Fin.elim0 i
  · have hN : 0 < N := Nat.pos_of_ne_zero hn
    obtain ⟨σ,hσ⟩:=greedy_permutation (fun t g => d ⟨t.val % N,Nat.mod_lt _ hN⟩ g)
    refine ⟨σ,?_⟩
    intro i t u ht htu
    have he : (⟨t.val % N,Nat.mod_lt _ hN⟩ : Fin N)=i := Fin.ext ht
    simpa only [he] using hσ t u htu
end Queelius.Chores

end

section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

theorem tight_nonpos (N : ℕ) (g : Fin ((N-1)*N+1)) : tightUtil N g≤0 := by
  simp only [tightUtil]
  split_ifs <;> linarith [show (0:ℝ)≤1/(N:ℝ) by positivity]

theorem tight_last (N : ℕ) : tightUtil N (Fin.last ((N-1)*N)) = -1 := by
  simp [tightUtil]

theorem tight_chores (N : ℕ) : IsChores (fun _ : Fin N=>tightUtil N) := by
  refine ⟨fun _ g=>tight_nonpos N g,?_⟩
  intro i
  exact ⟨Fin.last ((N-1)*N),by change tightUtil N (Fin.last ((N-1)*N))≠0;rw [tight_last];norm_num⟩

def tightPartition {N : ℕ} (hN : 0<N) (g : Fin ((N-1)*N+1)) : Fin N :=
  ⟨g.val/N,by
    apply (Nat.div_lt_iff_lt_mul hN).mpr
    have hn : N-1+1=N := Nat.sub_add_cancel hN
    have hg:=g.isLt
    nlinarith⟩

theorem partition_card_le {N : ℕ} (hN : 0<N) (i : Fin N) :
    (univ.filter (fun g=>tightPartition hN g=i)).card≤N := by
  classical
  let f : Fin ((N-1)*N+1) → Fin N := fun g=>⟨g.val%N,Nat.mod_lt _ hN⟩
  have hc:=card_le_card_of_injOn (s:=univ.filter (fun g=>tightPartition hN g=i))
    (t:=(univ:Finset (Fin N))) f (by intro g hg;exact mem_univ _) (by
      intro a ha b hb hab
      have hqa : a.val/N=i.val := congrArg Fin.val (mem_filter.mp ha).2
      have hqb : b.val/N=i.val := congrArg Fin.val (mem_filter.mp hb).2
      have hm : a.val%N=b.val%N := congrArg Fin.val hab
      apply Fin.ext
      have h1:=Nat.mod_add_div a.val N
      have h2:=Nat.mod_add_div b.val N
      rw [hqa,hm] at h1
      rw [hqb] at h2
      omega)
  simpa only [card_univ,Fintype.card_fin] using hc

theorem last_partition_fiber {N : ℕ} (hN : 0<N) (i : Fin N) (hi : i.val=N-1) :
    univ.filter (fun g=>tightPartition hN g=i)={Fin.last ((N-1)*N)} := by
  classical
  ext g
  simp only [mem_filter,mem_univ,true_and,mem_singleton]
  constructor
  · intro hg
    have hq : g.val/N=N-1 := (congrArg Fin.val hg).trans hi
    have hle:=Nat.div_mul_le_self g.val N
    rw [hq] at hle
    apply Fin.ext
    have hlt:=g.isLt
    simp only [Fin.val_last]
    omega
  · rintro rfl
    apply Fin.ext
    simpa only [tightPartition,Fin.val_last,Nat.mul_div_cancel _ hN] using hi.symm

theorem tight_partition_value {N : ℕ} (hN : 0<N) (i j : Fin N) :
    -1 ≤ bval (fun _ : Fin N=>tightUtil N) i (univ.filter (fun g=>tightPartition hN g=j)) := by
  classical
  by_cases hj : j.val=N-1
  · rw [last_partition_fiber hN j hj]
    simp [bval,tight_last]
  · let F:=univ.filter (fun g=>tightPartition hN g=j)
    have he : ∀ g ∈ F,tightUtil N g= -(1/(N:ℝ)) := by
      intro g hg
      have hq : g.val/N=j.val := congrArg Fin.val (mem_filter.mp hg).2
      have hglt : g.val<(N-1)*N := by
        by_contra hn
        have hgval : g.val=(N-1)*N := by have ht:=g.isLt;omega
        rw [hgval,Nat.mul_div_cancel _ hN] at hq
        exact hj hq.symm
      simp only [tightUtil,if_pos hglt]
    have hv : bval (fun _ : Fin N=>tightUtil N) i F=(F.card:ℝ)* -(1/(N:ℝ)) := by
      unfold bval
      rw [sum_congr rfl he]
      simp only [sum_const,nsmul_eq_mul]
    change -1≤bval (fun _ : Fin N=>tightUtil N) i F
    rw [hv]
    have hc : (F.card:ℝ)≤N := by exact_mod_cast partition_card_le hN j
    have hn : (0:ℝ)<N := by exact_mod_cast hN
    have hp:=mul_le_mul_of_nonneg_right hc (le_of_lt (one_div_pos.mpr hn))
    have heq : (N:ℝ)*(1/(N:ℝ))=1 := by field_simp
    rw [heq] at hp
    nlinarith

theorem tight_mms {N : ℕ} (hN : 0<N) (i : Fin N) :
    LittleCharity.MMS.mms (bval (fun _ : Fin N=>tightUtil N) i) N univ= -1 := by
  classical
  letI : NeZero N:=⟨Nat.ne_of_gt hN⟩
  apply le_antisymm
  · have h:=mms_item hN (fun _ : Fin N=>tightUtil N) i (tight_nonpos N) (Fin.last ((N-1)*N))
    simpa only [tight_last] using h
  · unfold LittleCharity.MMS.mms
    apply le_trans _ (le_ciSup (Set.finite_range _).bddAbove (tightPartition hN))
    apply le_ciInf
    exact tight_partition_value hN i
end Queelius.Chores

end

section
noncomputable section
open Finset
namespace Queelius.Chores

def slots (N m i : ℕ) : Finset ℕ := (range m).filter (fun t => t % N = i)

theorem residue_shift {N : ℕ} (hN : 0 < N) (i j : Fin N) :
    ∃ δ : ℕ, δ < N ∧ ∀ t : ℕ, t % N = i.val → (t+δ) % N = j.val := by
  by_cases hij : i.val ≤ j.val
  · refine ⟨j.val-i.val,by omega,?_⟩
    intro t ht
    have hd : j.val-i.val < N := by omega
    rw [Nat.add_mod,ht,Nat.mod_eq_of_lt hd]
    have he : i.val+(j.val-i.val)=j.val := by omega
    rw [he,Nat.mod_eq_of_lt j.isLt]
  · refine ⟨N+j.val-i.val,by omega,?_⟩
    intro t ht
    have hd : N+j.val-i.val < N := by omega
    rw [Nat.add_mod,ht,Nat.mod_eq_of_lt hd]
    have he : i.val+(N+j.val-i.val)=N+j.val := by omega
    rw [he]
    simp [Nat.add_mod,Nat.mod_eq_of_lt j.isLt]

theorem slot_pair_bound {N m : ℕ} (hN : 0 < N) (i j : Fin N) (v : ℕ → ℝ)
    (hv : ∀ t, v t ≤ 0) (L : ℝ) (hL : L ≤ 0) (hmin : ∀ t, t < m → L ≤ v t)
    (hgreedy : ∀ t ∈ slots N m i.val, ∀ u, t ≤ u → u < m → v u ≤ v t) :
    (∑ t ∈ slots N m j.val, v t)+L ≤ ∑ t ∈ slots N m i.val, v t := by
  classical
  by_cases hs : (slots N m i.val).Nonempty
  · let last := (slots N m i.val).max' hs
    let s := (slots N m i.val).erase last
    have hlast : last ∈ slots N m i.val := max'_mem _ hs
    have hlastm : last < m := (mem_filter.mp hlast).1 |> mem_range.mp
    have hlastmod : last % N=i.val := (mem_filter.mp hlast).2
    obtain ⟨δ,hδ,hmod⟩:=residue_shift hN i j
    have hbound (t : ℕ) (ht : t ∈ s) : t+δ < m := by
      have hti : t ∈ slots N m i.val := (mem_erase.mp ht).2
      have htm : t % N=i.val := (mem_filter.mp hti).2
      have hlt : t < last := (slots N m i.val).lt_max'_of_mem_erase_max' hs ht
      have hgap:=same_residue_gap hN hlt (htm.trans hlastmod.symm)
      omega
    have himage : s.image (fun t => t+δ) ⊆ slots N m j.val := by
      intro u hu
      obtain ⟨t,ht,rfl⟩:=mem_image.mp hu
      refine mem_filter.mpr ⟨mem_range.mpr (hbound t ht),?_⟩
      exact hmod t (mem_filter.mp (mem_erase.mp ht).2).2
    have hsum := negative_sum_subset v himage (fun t _ => hv t)
    have he : (∑ t ∈ s.image (fun t => t+δ), v t) = ∑ t ∈ s, v (t+δ) := by
      apply sum_image
      intro a ha b hb hab
      exact Nat.add_right_cancel hab
    rw [he] at hsum
    have hcomp : (∑ t ∈ s, v (t+δ)) ≤ ∑ t ∈ s, v t := by
      apply sum_le_sum
      intro t ht
      exact hgreedy t (mem_erase.mp ht).2 (t+δ) (by omega) (hbound t ht)
    have hsplit : (∑ t ∈ s, v t)+v last = ∑ t ∈ slots N m i.val, v t :=
      sum_erase_add _ _ hlast
    have hminlast:=hmin last hlastm
    linarith
  · have he : slots N m i.val=∅ := not_nonempty_iff_eq_empty.mp hs
    rw [he,sum_empty]
    have hsum : (∑ t ∈ slots N m j.val, v t) ≤ 0 := sum_nonpos (fun t _ => hv t)
    linarith
end Queelius.Chores

end

section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

def valueAt {N m : ℕ} (d : Fin N → Fin m → ℝ) (i : Fin N) (σ : Fin m ≃ Fin m) (t : ℕ) : ℝ :=
  if h : t < m then d i (σ ⟨t,h⟩) else 0

theorem valueAt_nonpos {N m : ℕ} (d : Fin N → Fin m → ℝ) (i : Fin N) (σ : Fin m ≃ Fin m)
    (hd : ∀ g, d i g ≤ 0) (t : ℕ) : valueAt d i σ t ≤ 0 := by
  unfold valueAt
  split_ifs <;> simp_all

theorem bundle_nat {N m : ℕ} (d : Fin N → Fin m → ℝ) (σ : Fin m ≃ Fin m) (i j : Fin N) :
    bval d i (rrBundle σ j) = ∑ t ∈ (range m).filter (fun t => t % N=j.val), valueAt d i σ t := by
  classical
  rw [bundle_picks]
  apply sum_bij (fun t _ => t.val)
  · intro t ht
    exact mem_filter.mpr ⟨mem_range.mpr t.isLt,(mem_filter.mp ht).2⟩
  · intro a ha b hb hab
    exact Fin.ext hab
  · intro u hu
    have hum : u < m := mem_range.mp (mem_filter.mp hu).1
    refine ⟨⟨u,hum⟩,?_,rfl⟩
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hu).2⟩
  · intro t ht
    simp [valueAt,t.isLt]
end Queelius.Chores

end

section
noncomputable section
open Finset
namespace Queelius.Chores.Controls
open MmSChores.RoundRobin

def badUtility (_ : Fin 2) (g : Fin 4) : ℝ := if g.val % 2=0 then -1 else 0

theorem bad_is_chores : IsChores badUtility := by
  constructor
  · intro i g
    unfold badUtility
    split_ifs <;> norm_num
  · intro i
    exact ⟨0,by norm_num [badUtility]⟩

theorem bad_own_value : bval badUtility (0 : Fin 2) (rrBundle (Equiv.refl (Fin 4)) (0 : Fin 2)) = -2 := by
  norm_num [bval,rrBundle,sum_filter,Fin.sum_univ_succ,badUtility]

theorem bad_other_value : bval badUtility (0 : Fin 2) (rrBundle (Equiv.refl (Fin 4)) (1 : Fin 2)) = 0 := by
  norm_num [bval,rrBundle,sum_filter,Fin.sum_univ_succ,badUtility]

theorem bad_minimum (hm : (univ : Finset (Fin 4)).Nonempty) : univ.inf' hm (badUtility 0) = -1 := by
  apply le_antisymm
  · exact (inf'_le (badUtility 0) (mem_univ (0 : Fin 4))).trans (by norm_num [badUtility])
  · apply le_inf'
    intro g hg
    unfold badUtility
    split_ifs <;> norm_num

theorem greedy_needed (hm : (univ : Finset (Fin 4)).Nonempty) :
    ¬ (bval badUtility 0 (rrBundle (Equiv.refl (Fin 4)) (1 : Fin 2)) + univ.inf' hm (badUtility 0) ≤
      bval badUtility 0 (rrBundle (Equiv.refl (Fin 4)) (0 : Fin 2))) := by
  rw [bad_own_value,bad_other_value,bad_minimum]
  norm_num

theorem bad_not_run : ¬ IsRoundRobinRun badUtility (Equiv.refl (Fin 4)) := by
  intro h
  have hh:=h (0 : Fin 2) (0 : Fin 4) (1 : Fin 4) (by decide) (by decide)
  norm_num [badUtility] at hh

theorem one_agent_mms {m : ℕ} (d : Fin 1 → Fin m → ℝ) :
    LittleCharity.MMS.mms (bval d 0) 1 univ=bval d 0 univ := by
  simp [LittleCharity.MMS.mms,Subsingleton.elim (α:=Fin 1)]

theorem zero_is_run {N m : ℕ} (σ : Fin m ≃ Fin m) :
    IsRoundRobinRun (fun (_ : Fin N) (_ : Fin m) => (0 : ℝ)) σ := by
  intro i t u ht htu
  exact le_rfl
end Queelius.Chores.Controls

end

section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

theorem greedy_last {N : ℕ} (hN : 0<N)
    (σ : Fin ((N-1)*N+1) ≃ Fin ((N-1)*N+1))
    (hσ : IsRoundRobinRun (fun _ : Fin N=>tightUtil N) σ) :
    σ (Fin.last ((N-1)*N))=Fin.last ((N-1)*N) := by
  by_cases hn1 : N=1
  · subst N
    apply Fin.ext
    have h:=(σ (Fin.last ((1-1)*1))).isLt
    simp only [Fin.val_last]
    omega
  · have hn : 1<N := by omega
    by_contra hne
    let t:=σ.symm (Fin.last ((N-1)*N))
    have hsmall : (σ (Fin.last ((N-1)*N))).val<(N-1)*N := by
      have hb:=(σ (Fin.last ((N-1)*N))).isLt
      by_contra h
      apply hne
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    have hg:=hσ ⟨t.val%N,Nat.mod_lt _ hN⟩ t (Fin.last ((N-1)*N)) rfl (Fin.le_last _)
    have ht : σ t=Fin.last ((N-1)*N) := σ.apply_symm_apply _
    dsimp only at hg
    rw [ht,tight_last] at hg
    simp only [tightUtil,if_pos hsmall] at hg
    have hreal : (1:ℝ)<N := by exact_mod_cast hn
    have hdiv : 1/(N:ℝ)<1 := (div_lt_one (by linarith)).mpr hreal
    linarith

theorem greedy_values {N : ℕ} (hN : 0<N)
    (σ : Fin ((N-1)*N+1) ≃ Fin ((N-1)*N+1))
    (hσ : IsRoundRobinRun (fun _ : Fin N=>tightUtil N) σ)
    (t : Fin ((N-1)*N+1)) : tightUtil N (σ t)=tightUtil N t := by
  have hl:=greedy_last hN σ hσ
  by_cases ht : t=Fin.last ((N-1)*N)
  · rw [ht,hl]
  · have hv : t.val<(N-1)*N := by
      have hb:=t.isLt
      by_contra h
      apply ht
      apply Fin.ext
      simp only [Fin.val_last]
      omega
    have hsv : (σ t).val<(N-1)*N := by
      have hb:=(σ t).isLt
      by_contra h
      have he : σ t=Fin.last ((N-1)*N) := by apply Fin.ext;simp only [Fin.val_last];omega
      exact ht (σ.injective (he.trans hl.symm))
    simp only [tightUtil,if_pos hv,if_pos hsv]

theorem tight_agent_zero {N : ℕ} (hN : 0<N)
    (σ : Fin ((N-1)*N+1) ≃ Fin ((N-1)*N+1))
    (hσ : IsRoundRobinRun (fun _ : Fin N=>tightUtil N) σ) :
    bval (fun _ : Fin N=>tightUtil N) ⟨0,hN⟩ (rrBundle σ ⟨0,hN⟩)= -(2-1/(N:ℝ)) := by
  classical
  let last : Fin N:=⟨N-1,by omega⟩
  let v : Fin N → ℝ := fun q=>if q=last then -1 else -(1/(N:ℝ))
  rw [bundle_picks]
  have hs : (∑ t ∈ univ.filter (fun t : Fin ((N-1)*N+1)=>t.val%N=0),tightUtil N (σ t))=
      ∑ q : Fin N,v q := by
    apply sum_bij (fun t _=>tightPartition hN t)
    · intro t ht
      exact mem_univ _
    · intro a ha b hb hab
      have hqa : a.val/N=b.val/N := congrArg Fin.val hab
      have hma : a.val%N=0 := (mem_filter.mp ha).2
      have hmb : b.val%N=0 := (mem_filter.mp hb).2
      apply Fin.ext
      have h1:=Nat.mod_add_div a.val N
      have h2:=Nat.mod_add_div b.val N
      rw [hqa,hma] at h1
      rw [hmb] at h2
      omega
    · intro q hq
      have hqv : q.val≤N-1 := by have h:=q.isLt;omega
      have ht : q.val*N<(N-1)*N+1 := by nlinarith
      refine ⟨⟨q.val*N,ht⟩,?_,?_⟩
      · simp
      · apply Fin.ext
        exact Nat.mul_div_cancel _ hN
    · intro t ht
      rw [greedy_values hN σ hσ]
      have hm : t.val%N=0 := (mem_filter.mp ht).2
      have htq : t.val=N*(t.val/N) := by have h:=Nat.mod_add_div t.val N;omega
      by_cases he : tightPartition hN t=last
      · have hq : t.val/N=N-1 := congrArg Fin.val he
        have htlast : t=Fin.last ((N-1)*N) := by
          apply Fin.ext
          simp only [Fin.val_last]
          rw [htq,hq,mul_comm]
        simp only [v,he,ite_true]
        rw [htlast,tight_last]
      · have hv : t.val<(N-1)*N := by
          have hb:=t.isLt
          by_contra h
          have heq : t.val=(N-1)*N := by omega
          apply he
          apply Fin.ext
          simp only [tightPartition]
          rw [heq,Nat.mul_div_cancel _ hN]
        simp only [tightUtil,if_pos hv,v,he,ite_false]
  change (∑ t ∈ univ.filter (fun t : Fin ((N-1)*N+1)=>t.val%N=0),tightUtil N (σ t))= _
  rw [hs]
  have hv : (∑ q : Fin N,v q)= -(1/(N:ℝ))*((N:ℝ)-1)-1 := by
    rw [←sum_erase_add _ _ (mem_univ last)]
    have he : ∑ q ∈ univ.erase last,v q = ((N-1:ℕ):ℝ)* -(1/(N:ℝ)) := by
      calc
        _=∑ _q ∈ univ.erase last,-(1/(N:ℝ)) := sum_congr rfl (fun q hq=>by simp [v,(mem_erase.mp hq).1])
        _=_ := by simp
    rw [he]
    have hn : (N-1:ℕ)=N-1 := rfl
    rw [Nat.cast_sub (by omega : 1≤N)]
    simp [v]
    ring
  rw [hv]
  have hn : (N:ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hN)
  field_simp
  <;> ring
end Queelius.Chores

end

section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

theorem pairwise_bound {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (hd : ∀ i j, d i j ≤ 0) (σ : Fin m ≃ Fin m)
    (hσ : IsRoundRobinRun d σ) (i j : Fin N) :
    bval d i (rrBundle σ j)+univ.inf' hm (d i) ≤ bval d i (rrBundle σ i) := by
  classical
  rw [bundle_nat,bundle_nat]
  apply slot_pair_bound hN i j (valueAt d i σ) (valueAt_nonpos d i σ (hd i))
  · obtain ⟨g,hg⟩:=hm
    exact (inf'_le (d i) hg).trans (hd i g)
  · intro t ht
    simp only [valueAt,dif_pos ht]
    exact inf'_le _ (mem_univ _)
  · intro t ht u htu hum
    have htm : t < m := mem_range.mp (mem_filter.mp ht).1
    have htmod : t % N=i.val := (mem_filter.mp ht).2
    simp only [valueAt,dif_pos htm,dif_pos hum]
    exact hσ i ⟨t,htm⟩ ⟨u,hum⟩ htmod htu

theorem rr_total {N m : ℕ} (hN : 0 < N) (d : Fin N → Fin m → ℝ)
    (σ : Fin m ≃ Fin m) (i : Fin N) : ∑ j : Fin N, bval d i (rrBundle σ j)=bval d i univ := by
  have he (j : Fin N) : rrBundle σ j=univ.filter (fun g => owner hN σ g=j) := by
    ext g
    simp only [mem_filter,mem_univ,true_and,rr_membership hN]
  simp_rw [he]
  exact partition_sum d i (owner hN σ)

theorem averaged_bound {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (hd : ∀ i j, d i j ≤ 0) (σ : Fin m ≃ Fin m)
    (hσ : IsRoundRobinRun d σ) (i : Fin N) :
    (1/(N : ℝ))*bval d i univ+(1-1/(N : ℝ))*univ.inf' hm (d i) ≤ bval d i (rrBundle σ i) := by
  classical
  let L:=univ.inf' hm (d i)
  have hh (j : Fin N) : bval d i (rrBundle σ j)+L ≤
      bval d i (rrBundle σ i)+(if j=i then L else 0) := by
    by_cases hj : j=i
    · subst j
      simp
    · simpa only [hj,ite_false,add_zero] using pairwise_bound hN hm d hd σ hσ i j
  have hs:=sum_le_sum (s:=univ) (fun j _ => hh j)
  simp only [sum_add_distrib,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul,
    sum_ite_eq',mem_univ,ite_true] at hs
  rw [rr_total hN d σ i] at hs
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  apply (mul_le_mul_iff_right₀ hn).mp
  calc
    (N : ℝ)*((1/(N : ℝ))*bval d i univ+(1-1/(N : ℝ))*univ.inf' hm (d i)) =
        bval d i univ+((N : ℝ)-1)*L := by dsimp [L]; field_simp [hn.ne']
    _ ≤ (N : ℝ)*bval d i (rrBundle σ i) := by linarith

theorem approximation_bound {N m : ℕ} (hN : 0 < N) (d : Fin N → Fin m → ℝ)
    (hd : ∀ i j, d i j ≤ 0) (σ : Fin m ≃ Fin m) (hσ : IsRoundRobinRun d σ) (i : Fin N) :
    (2-1/(N : ℝ))*LittleCharity.MMS.mms (bval d i) N univ ≤ bval d i (rrBundle σ i) := by
  classical
  letI : NeZero N := ⟨Nat.ne_of_gt hN⟩
  by_cases hm : m=0
  · subst m
    simp [LittleCharity.MMS.mms,bval,rrBundle]
  · letI : NeZero m := ⟨hm⟩
    have hne : (univ : Finset (Fin m)).Nonempty := univ_nonempty
    have hn : (0 : ℝ) < N := by exact_mod_cast hN
    have hone : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have hcoef : 0 ≤ 1-1/(N : ℝ) := by
      have hh : 1/(N : ℝ) ≤ 1 := (div_le_one hn).mpr hone
      linarith
    have ha:=mms_average hN d i
    have hb:=mul_le_mul_of_nonneg_left (mms_minimum hN hne d i (hd i)) hcoef
    have hc:=averaged_bound hN hne d hd σ hσ i
    nlinarith
end Queelius.Chores

end

section
namespace MmSChores.RoundRobin

open Finset

/-- Eq. (1), proof of Theorem 9 (PDF p. 4): in every round-robin run on non-positive utilities,
`d_i(S_i) ≥ d_i(S_{i'}) + d_i^min` for all agents `i, i'`, where
`d_i^min = min_{j ∈ M} d_i(j)`. -/
theorem eq_1 {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (hd : ∀ i j, d i j ≤ 0) (σ : Fin m ≃ Fin m)
    (hσ : IsRoundRobinRun d σ) (i i' : Fin N) :
    bval d i (rrBundle σ i') + univ.inf' hm (d i) ≤ bval d i (rrBundle σ i) := by
  exact Queelius.Chores.pairwise_bound hN hm d hd σ hσ i i'

end MmSChores.RoundRobin

namespace MmSChores.RoundRobin

open Finset

/-- Proof of Theorem 9 (PDF p. 4), first half of the last sentence: `1/N · d_i(M) ≥ MmS^N_{d_i}(M)`.
It holds for every real additive utility, with no sign condition. -/
theorem mms_le_average {N m : ℕ} (hN : 0 < N) (d : Fin N → Fin m → ℝ) (i : Fin N) :
    LittleCharity.MMS.mms (bval d i) N univ ≤ (1 / (N : ℝ)) * bval d i univ := by
  exact Queelius.Chores.mms_average hN d i

end MmSChores.RoundRobin

namespace MmSChores.RoundRobin

open Finset

/-- Proof of Theorem 9 (PDF p. 4), second half of the last sentence: `d_i^min ≥ MmS^N_{d_i}(M)`
when all of agent `i`'s utilities are non-positive. -/
theorem mms_le_dmin {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (i : Fin N) (hd : ∀ j, d i j ≤ 0) :
    LittleCharity.MMS.mms (bval d i) N univ ≤ univ.inf' hm (d i) := by
  exact Queelius.Chores.mms_minimum hN hm d i hd

end MmSChores.RoundRobin

namespace MmSChores.RoundRobin

open Finset

/-- Display after (1), proof of Theorem 9 (PDF p. 4): in every round-robin run on non-positive
utilities, `d_i(S_i) ≥ (1/N) · d_i(M) + (1 - 1/N) · d_i^min` for every agent `i`. -/
theorem display_after_eq_1 {N m : ℕ} (hN : 0 < N) (hm : (univ : Finset (Fin m)).Nonempty)
    (d : Fin N → Fin m → ℝ) (hd : ∀ i j, d i j ≤ 0) (σ : Fin m ≃ Fin m)
    (hσ : IsRoundRobinRun d σ) (i : Fin N) :
    (1 / (N : ℝ)) * bval d i univ + (1 - 1 / (N : ℝ)) * univ.inf' hm (d i)
      ≤ bval d i (rrBundle σ i) := by
  exact Queelius.Chores.averaged_bound hN hm d hd σ hσ i

end MmSChores.RoundRobin

end

section
noncomputable section
section
theorem existence_clause : (
∀ (N m : Nat) (d : Fin N → Fin m → Real),
  @Exists (Equiv (Fin m) (Fin m)) fun (σ : Equiv (Fin m) (Fin m)) => @MmSChores.RoundRobin.IsRoundRobinRun N m d σ
) := @Queelius.Chores.run_exists
end
section
theorem approximation_clause : (
∀ (N m : Nat),
  @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
    ∀ (d : Fin N → Fin m → Real),
      (∀ (i : Fin N) (j : Fin m),
          @LE.le Real Real.instLE (d i j) (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
        ∀ (σ : Equiv (Fin m) (Fin m)),
          @MmSChores.RoundRobin.IsRoundRobinRun N m d σ →
            ∀ (i : Fin N),
              @LE.le Real Real.instLE
                (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                  (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                    (@OfNat.ofNat Real (nat_lit 2)
                      (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                        (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                          (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                    (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                      (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                      (@Nat.cast Real Real.instNatCast N)))
                  (@LittleCharity.MMS.mms m (@MmSChores.RoundRobin.bval N m d i) N
                    (@Finset.univ (Fin m) (Fin.fintype m))))
                (@MmSChores.RoundRobin.bval N m d i (@MmSChores.RoundRobin.rrBundle N m σ i))
) := @Queelius.Chores.approximation_bound
end

end

section
noncomputable section
open Finset
namespace Queelius.Chores
open MmSChores.RoundRobin

theorem sharpness (N : ℕ) (hN : 0<N) (c : ℝ) (hc : c<2-1/(N:ℝ)) :
    ∃ (m : ℕ) (d : Fin N → Fin m → ℝ),IsChores d ∧
      ∀ σ : Fin m ≃ Fin m,IsRoundRobinRun d σ →
        ∃ i : Fin N,bval d i (rrBundle σ i)<c*LittleCharity.MMS.mms (bval d i) N univ := by
  refine ⟨(N-1)*N+1,(fun _ : Fin N=>tightUtil N),tight_chores N,?_⟩
  intro σ hσ
  refine ⟨⟨0,hN⟩,?_⟩
  rw [tight_agent_zero hN σ hσ,tight_mms hN]
  linarith
end Queelius.Chores
namespace MmSChores.RoundRobin

theorem tight_instance_mms {N : ℕ} (hN : 0<N) :
    IsChores (fun _ : Fin N=>tightUtil N) ∧
      ∀ i : Fin N,LittleCharity.MMS.mms (bval (fun _ : Fin N=>tightUtil N) i) N univ= -1 :=
  ⟨Queelius.Chores.tight_chores N,Queelius.Chores.tight_mms hN⟩

theorem tight_instance_run {N : ℕ} (hN : 0<N)
    (σ : Fin ((N-1)*N+1) ≃ Fin ((N-1)*N+1))
    (hσ : IsRoundRobinRun (fun _ : Fin N=>tightUtil N) σ) :
    bval (fun _ : Fin N=>tightUtil N) ⟨0,hN⟩ (rrBundle σ ⟨0,hN⟩)= -(2-1/(N:ℝ)) :=
  Queelius.Chores.tight_agent_zero hN σ hσ
end MmSChores.RoundRobin

end

section
noncomputable section
open Finset
namespace Queelius.Chores.Controls
open MmSChores.RoundRobin

theorem tight_identity_run (N : ℕ) :
    IsRoundRobinRun (fun _ : Fin N=>tightUtil N) (Equiv.refl _) := by
  intro i t u ht htu
  change tightUtil N u≤tightUtil N t
  simp only [tightUtil]
  split_ifs with hu ht'
  · exact le_rfl
  · have hv : t.val≤u.val:=htu
    omega
  · have hn : (1:ℝ)≤N := by exact_mod_cast (show 1≤N by have hi:=i.isLt;omega)
    have hpos : (0:ℝ)<N := by linarith
    have hd : 1/(N:ℝ)≤1 := (div_le_one hpos).mpr hn
    linarith
  · exact le_rfl

theorem one_agent_tight :
    LittleCharity.MMS.mms (bval (fun _ : Fin 1=>tightUtil 1) 0) 1 univ= -1 ∧
    bval (fun _ : Fin 1=>tightUtil 1) 0 (rrBundle (Equiv.refl _) (0:Fin 1))= -1 := by
  constructor
  · exact tight_mms (by decide) 0
  · have h:=tight_agent_zero (N:=1) (by decide) (Equiv.refl _) (tight_identity_run 1)
    norm_num at h ⊢
    exact h

theorem two_agent_tight :
    bval (fun _ : Fin 2=>tightUtil 2) 0 (rrBundle (Equiv.refl _) (0:Fin 2))= -(3/2:ℝ) := by
  have h:=tight_agent_zero (N:=2) (by decide) (Equiv.refl _) (tight_identity_run 2)
  norm_num at h ⊢
  exact h

def nongreedySwap : Fin 3 ≃ Fin 3 := Equiv.swap 1 2

theorem nongreedy_value :
    bval (fun _ : Fin 2=>tightUtil 2) 0 (rrBundle nongreedySwap (0:Fin 2))= -1 := by
  have h0 : nongreedySwap.symm (0:Fin 3)=0 := by decide
  have h1 : nongreedySwap.symm (1:Fin 3)=2 := by decide
  have h2 : nongreedySwap.symm (2:Fin 3)=1 := by decide
  norm_num [bval,rrBundle,sum_filter,Fin.sum_univ_succ,tightUtil,h0,h1,h2]

theorem nongreedy_not_run : ¬ IsRoundRobinRun (fun _ : Fin 2=>tightUtil 2) nongreedySwap := by
  intro h
  have hg:=h (1:Fin 2) (1:Fin 3) (2:Fin 3) (by decide) (by decide)
  norm_num [nongreedySwap,Equiv.swap_apply_def,tightUtil] at hg
end Queelius.Chores.Controls

end

section
theorem submission_primary_solution : (
  And
    (∀ (N m : Nat) (d : Fin N → Fin m → Real),
      @Exists (Equiv (Fin m) (Fin m)) fun (σ : Equiv (Fin m) (Fin m)) => @MmSChores.RoundRobin.IsRoundRobinRun N m d σ)
    (And
      (∀ (N m : Nat),
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
          ∀ (d : Fin N → Fin m → Real),
            (∀ (i : Fin N) (j : Fin m),
                @LE.le Real Real.instLE (d i j) (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
              ∀ (σ : Equiv (Fin m) (Fin m)),
                @MmSChores.RoundRobin.IsRoundRobinRun N m d σ →
                  ∀ (i : Fin N),
                    @LE.le Real Real.instLE
                      (@HMul.hMul Real Real Real (@instHMul Real Real.instMul)
                        (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                          (@OfNat.ofNat Real (nat_lit 2)
                            (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                              (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                                (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                          (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                            (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                            (@Nat.cast Real Real.instNatCast N)))
                        (@LittleCharity.MMS.mms m (@MmSChores.RoundRobin.bval N m d i) N
                          (@Finset.univ (Fin m) (Fin.fintype m))))
                      (@MmSChores.RoundRobin.bval N m d i (@MmSChores.RoundRobin.rrBundle N m σ i)))
      (∀ (N : Nat),
        @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
          ∀ (c : Real),
            @LT.lt Real Real.instLT c
                (@HSub.hSub Real Real Real (@instHSub Real Real.instSub)
                  (@OfNat.ofNat Real (nat_lit 2)
                    (@instOfNatAtLeastTwo Real (nat_lit 2) Real.instNatCast
                      (@Nat.instAtLeastTwoHAddOfNat (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))
                        (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0)))))))
                  (@HDiv.hDiv Real Real Real (@instHDiv Real (@DivInvMonoid.toDiv Real Real.instDivInvMonoid))
                    (@OfNat.ofNat Real (nat_lit 1) (@One.toOfNat1 Real Real.instOne))
                    (@Nat.cast Real Real.instNatCast N))) →
              @Exists Nat fun (m : Nat) =>
                @Exists (Fin N → Fin m → Real) fun (d : Fin N → Fin m → Real) =>
                  And (@MmSChores.RoundRobin.IsChores N m d)
                    (∀ (σ : Equiv (Fin m) (Fin m)),
                      @MmSChores.RoundRobin.IsRoundRobinRun N m d σ →
                        @Exists (Fin N) fun (i : Fin N) =>
                          @LT.lt Real Real.instLT
                            (@MmSChores.RoundRobin.bval N m d i (@MmSChores.RoundRobin.rrBundle N m σ i))
                            (@HMul.hMul Real Real Real (@instHMul Real Real.instMul) c
                              (@LittleCharity.MMS.mms m (@MmSChores.RoundRobin.bval N m d i) N
                                (@Finset.univ (Fin m) (Fin.fintype m)))))))
) := ⟨@Queelius.Chores.run_exists,@Queelius.Chores.approximation_bound,@Queelius.Chores.sharpness⟩

end


theorem solution : (
  ∀ {N m : Nat},
    @LT.lt Nat instLTNat (@OfNat.ofNat Nat (nat_lit 0) (instOfNatNat (nat_lit 0))) N →
      ∀ (hm : @Finset.Nonempty (Fin m) (@Finset.univ (Fin m) (Fin.fintype m))) (d : Fin N → Fin m → Real) (i : Fin N),
        (∀ (j : Fin m),
            @LE.le Real Real.instLE (d i j) (@OfNat.ofNat Real (nat_lit 0) (@Zero.toOfNat0 Real Real.instZero))) →
          @LE.le Real Real.instLE
            (@LittleCharity.MMS.mms m (@MmSChores.RoundRobin.bval N m d i) N (@Finset.univ (Fin m) (Fin.fintype m)))
            (@Finset.inf' Real (Fin m) Real.instSemilatticeInf (@Finset.univ (Fin m) (Fin.fintype m)) hm (d i))
) := @MmSChores.RoundRobin.mms_le_dmin
