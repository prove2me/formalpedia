-- Prove2me | solution 1 for MvFormalGroup.Hom.exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/70e9374b-7eb9-556c-869c-02ac4b5871a0

import Mathlib
import Definitions.Def_MvFormalGroup_BasicV2
import Definitions.Def_MvFormalGroup_EndRingV2
import Theorems.Thm_MvFormalGroup_Hom_exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd
import Theorems.Thm_MvPowerSeries_finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq
import Theorems.Thm_MvPowerSeries_span_range_X_eq_ker_constantCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
p2m_attr_erase "instance" "MvFormalGroup.Hom.instNeg MvFormalGroup.End.instAddCommGroup MvFormalGroup.Hom.instAddCommGroup MvFormalGroup.End.instRing instTopologicallyFGOfFiniteType"
p2m_attr_erase "simp" "MvFormalGroup.Hom.toPowerSeries_sub MvFormalGroup.linearPartHom_intCast MvFormalGroup.constantCoeff_negSeries MvFormalGroup.toPowerSeries_invHom MvFormalGroup.linearPartHom_neg MvFormalGroup.End.toPowerSeries_sub MvFormalGroup.End.toPowerSeries_neg MvFormalGroup.constantCoeff_invSeries MvFormalGroup.negApprox_zero MvFormalGroup.Hom.toPowerSeries_neg MvFormalGroup.Hom.toPowerSeries_neg'"

set_option autoImplicit false

noncomputable section

universe u

namespace P2mKcPartialFrobQuot

open MvPowerSeries MvFormalGroup

section Blocks

variable {k : Type u} [CommRing k] {d : ℕ}

def blkExt (c : Fin d → MvPowerSeries (Fin d) k) : Fin d ⊕ Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))
    (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))

theorem blkExt_inl (c : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) :
    blkExt c (Sum.inl j) = subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j) := rfl

theorem blkExt_inr (c : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) :
    blkExt c (Sum.inr j) = subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j) := rfl

theorem hasSubst_inl : HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_inr : HasSubst (fun l : Fin d => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem constantCoeff_blkExt {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0)
    (s : Fin d ⊕ Fin d) : (blkExt c s).constantCoeff = 0 := by
  rcases s with j | j
  · exact constantCoeff_subst_eq_zero (hasSubst_inl (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  · exact constantCoeff_subst_eq_zero (hasSubst_inr (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)

theorem hasSubst_blkExt {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0) :
    HasSubst (blkExt c) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_blkExt hc)

theorem subst_elim_blkExt {τ : Type*} {a b : Fin d → MvPowerSeries τ k}
    (ha : HasSubst a) (hb : HasSubst b) (c : Fin d → MvPowerSeries (Fin d) k) (s : Fin d ⊕ Fin d) :
    subst (Sum.elim a b) (blkExt c s) = Sum.elim (fun j => subst a (c j)) (fun j => subst b (c j)) s := by
  have hab : HasSubst (Sum.elim a b) := by
    refine ⟨?_, ?_⟩
    · rintro (l | l)
      · exact ha.const_coeff l
      · exact hb.const_coeff l
    · intro e
      have h1 := (ha.coeff_zero e)
      have h2 := (hb.coeff_zero e)
      refine ((h1.image Sum.inl).union (h2.image Sum.inr)).subset ?_
      rintro (l | l) hl
      · exact Or.inl ⟨l, hl, rfl⟩
      · exact Or.inr ⟨l, hl, rfl⟩
  rcases s with j | j
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) =
      subst a (c j)
    rw [subst_comp_subst_apply (hasSubst_inl (k := k) (d := d)) hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inl l)
  · show subst (Sum.elim a b) (subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) =
      subst b (c j)
    rw [subst_comp_subst_apply (hasSubst_inr (k := k) (d := d)) hab]
    congr 1
    funext l
    exact subst_X hab (Sum.inr l)

theorem subst_blkExt_blkExt {c c' : Fin d → MvPowerSeries (Fin d) k}
    (hc : ∀ i, (c i).constantCoeff = 0) (s : Fin d ⊕ Fin d) :
    subst (blkExt c) (blkExt c' s) = blkExt (fun j => subst c (c' j)) s := by
  have hcs := hasSubst_of_constantCoeff_zero hc
  have h := subst_elim_blkExt (k := k) (d := d)
    (a := fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))
    (b := fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j))
    (hasSubst_of_constantCoeff_zero fun j =>
      constantCoeff_subst_eq_zero (hasSubst_inl (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j))
    (hasSubst_of_constantCoeff_zero fun j =>
      constantCoeff_subst_eq_zero (hasSubst_inr (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j))
    c' s
  refine h.trans ?_
  rcases s with j | j
  · show subst (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) (c' j) =
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (subst c (c' j))
    rw [subst_comp_subst_apply hcs (hasSubst_inl (k := k) (d := d))]
  · show subst (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (c j)) (c' j) =
      subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (subst c (c' j))
    rw [subst_comp_subst_apply hcs (hasSubst_inr (k := k) (d := d))]

theorem blkExt_X : blkExt (fun i : Fin d => (X i : MvPowerSeries (Fin d) k)) =
    fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) k) := by
  funext s
  rcases s with j | j
  · exact subst_X (hasSubst_inl (k := k) (d := d)) j
  · exact subst_X (hasSubst_inr (k := k) (d := d)) j

theorem blkExt_X_pow (n : ℕ) : blkExt (fun i : Fin d => (X i : MvPowerSeries (Fin d) k) ^ n) =
    fun s => (X s : MvPowerSeries (Fin d ⊕ Fin d) k) ^ n := by
  funext s
  rcases s with j | j
  · show subst _ (X j ^ n) = _
    rw [subst_pow (hasSubst_inl (k := k) (d := d)), subst_X (hasSubst_inl (k := k) (d := d))]
  · show subst _ (X j ^ n) = _
    rw [subst_pow (hasSubst_inr (k := k) (d := d)), subst_X (hasSubst_inr (k := k) (d := d))]

theorem subst_blkExt_injective {α β : Fin d → MvPowerSeries (Fin d) k}
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) :
    Function.Injective (fun g : MvPowerSeries (Fin d ⊕ Fin d) k => subst (blkExt β) g) := by
  intro g g' hgg'
  have h := congrArg (subst (blkExt α)) hgg'
  simp only at h
  rwa [subst_comp_subst_apply (hasSubst_blkExt hβ0) (hasSubst_blkExt hα0),
    subst_comp_subst_apply (hasSubst_blkExt hβ0) (hasSubst_blkExt hα0),
    funext (subst_blkExt_blkExt hα0), funext hαβ, blkExt_X, subst_self] at h

end Blocks

section PartialExpand

variable {k : Type u} [CommRing k] {ι : Type*} [Fintype ι]

def pE (S : ι → Prop) [DecidablePred S] (q : ℕ) : ι → MvPowerSeries ι k :=
  fun j => if S j then X j else X j ^ q

def pexpo (S : ι → Prop) [DecidablePred S] (q : ℕ) (n : ι →₀ ℕ) : ι →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun j => if S j then n j else q * n j

def pctr (S : ι → Prop) [DecidablePred S] (q : ℕ) (f : MvPowerSeries ι k) : MvPowerSeries ι k :=
  fun n => coeff (pexpo S q n) f

variable {S : ι → Prop} [DecidablePred S] {q : ℕ}

@[scoped simp] theorem pexpo_apply (n : ι →₀ ℕ) (j : ι) : pexpo S q n j = if S j then n j else q * n j := by
  simp [pexpo]

theorem pexpo_injective (hq : 0 < q) : Function.Injective (pexpo S q) := by
  intro n n' h
  ext j
  have hj := congrArg (fun m => m j) h
  simp only [pexpo_apply] at hj
  split_ifs at hj with hS
  · exact hj
  · exact Nat.eq_of_mul_eq_mul_left hq hj

theorem pexpo_add (n n' : ι →₀ ℕ) : pexpo S q (n + n') = pexpo S q n + pexpo S q n' := by
  ext j
  simp only [pexpo_apply, Finsupp.add_apply]
  split_ifs <;> ring

omit [Fintype ι] in
theorem constantCoeff_pE (hq : 0 < q) (j : ι) : (pE (k := k) S q j).constantCoeff = 0 := by
  unfold pE
  split_ifs
  · exact constantCoeff_X _
  · rw [map_pow, constantCoeff_X, zero_pow hq.ne']

theorem hasSubst_pE (hq : 0 < q) : HasSubst (pE (k := k) S q) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_pE hq)

theorem prod_pE_pow (hq : 0 < q) (n : ι →₀ ℕ) :
    n.prod (fun i e => (pE (k := k) S q i) ^ e) = monomial (pexpo S q n) 1 := by
  rw [Finsupp.prod]
  have hfac : ∀ i ∈ n.support, (pE (k := k) S q i) ^ (n i) =
      ((MvPolynomial.X i ^ (pexpo S q n i) : MvPolynomial ι k) : MvPowerSeries ι k) := by
    intro i _
    unfold pE
    rw [pexpo_apply, MvPolynomial.coe_pow, MvPolynomial.coe_X]
    split_ifs
    · rfl
    · rw [← pow_mul]
  rw [Finset.prod_congr rfl hfac]
  have hsupp : n.support = (pexpo S q n).support := by
    ext i
    simp only [Finsupp.mem_support_iff, pexpo_apply, ne_eq]
    split_ifs
    · rfl
    · simp [hq.ne']
  rw [hsupp]
  simp only [← MvPolynomial.coeToMvPowerSeries.ringHom_apply, ← map_prod,
    MvPolynomial.prod_X_pow_eq_monomial]
  rw [MvPolynomial.coeToMvPowerSeries.ringHom_apply, MvPolynomial.coe_monomial]

theorem coeff_pexpo_subst_pE (hq : 0 < q) (g : MvPowerSeries ι k) (n : ι →₀ ℕ) :
    coeff (pexpo S q n) (subst (pE S q) g) = coeff n g := by
  classical
  rw [coeff_subst (hasSubst_pE hq)]
  rw [finsum_eq_single _ n]
  · rw [prod_pE_pow hq, coeff_monomial, if_pos rfl, smul_eq_mul, mul_one]
  · intro n' hn'
    rw [prod_pE_pow hq, coeff_monomial, if_neg (fun h => hn' (pexpo_injective hq h).symm), smul_zero]

theorem coeff_subst_pE_eq_zero (hq : 0 < q) (g : MvPowerSeries ι k) (m : ι →₀ ℕ)
    (hm : ∀ n, pexpo S q n ≠ m) : coeff m (subst (pE (k := k) S q) g) = 0 := by
  classical
  rw [coeff_subst (hasSubst_pE hq)]
  refine finsum_eq_zero_of_forall_eq_zero fun n' => ?_
  rw [prod_pE_pow hq, coeff_monomial, if_neg (fun h => hm n' h.symm), smul_zero]

theorem exists_pexpo_eq_of_forall_dvd (m : ι →₀ ℕ) (hm : ∀ j, ¬ S j → q ∣ m j) :
    ∃ n, pexpo S q n = m := by
  refine ⟨Finsupp.equivFunOnFinite.symm fun j => if S j then m j else m j / q, ?_⟩
  ext j
  simp only [pexpo_apply, Finsupp.coe_equivFunOnFinite_symm]
  split_ifs with hS
  · rfl
  · exact Nat.mul_div_cancel' (hm j hS)

theorem subst_pE_injective (hq : 0 < q) :
    Function.Injective (fun g : MvPowerSeries ι k => subst (pE (k := k) S q) g) := by
  intro g g' h
  ext n
  have := congrArg (coeff (pexpo S q n)) h
  simp only [coeff_pexpo_subst_pE hq] at this
  exact this

theorem coeff_pctr (f : MvPowerSeries ι k) (n : ι →₀ ℕ) : coeff n (pctr S q f) = coeff (pexpo S q n) f :=
  rfl

theorem subst_pE_pctr (hq : 0 < q) (f : MvPowerSeries ι k)
    (hf : ∀ m : ι →₀ ℕ, (∃ j, ¬ S j ∧ ¬ q ∣ m j) → coeff m f = 0) :
    subst (pE S q) (pctr S q f) = f := by
  ext m
  by_cases h : ∃ n, pexpo S q n = m
  · obtain ⟨n, rfl⟩ := h
    rw [coeff_pexpo_subst_pE hq]
    rfl
  · push Not at h
    rw [coeff_subst_pE_eq_zero hq _ _ h]
    symm
    apply hf
    by_contra hcon
    push Not at hcon
    obtain ⟨n, hn⟩ := exists_pexpo_eq_of_forall_dvd (S := S) (q := q) m hcon
    exact h n hn

theorem pctr_add (f g : MvPowerSeries ι k) : pctr S q (f + g) = pctr S q f + pctr S q g := by
  ext n; simp [coeff_pctr]

theorem pctr_smul (c : k) (f : MvPowerSeries ι k) : pctr S q (c • f) = c • pctr S q f := by
  ext n; simp [coeff_pctr]

theorem pctr_sum {κ : Type*} (s : Finset κ) (f : κ → MvPowerSeries ι k) :
    pctr S q (∑ x ∈ s, f x) = ∑ x ∈ s, pctr S q (f x) := by
  ext n; simp [coeff_pctr, map_sum]

theorem pctr_X_of (hq : 0 < q) (j : ι) (hj : S j) : pctr S q (X j : MvPowerSeries ι k) = X j := by
  classical
  apply subst_pE_injective (S := S) hq
  simp only
  rw [subst_pE_pctr hq, subst_X (hasSubst_pE hq)]
  · unfold pE; rw [if_pos hj]
  · intro m ⟨j', hj', hdiv⟩
    rw [coeff_X]
    rw [if_neg]
    rintro rfl
    rw [Finsupp.single_apply] at hdiv
    split_ifs at hdiv with hjj
    · exact hj' (hjj ▸ hj)
    · exact hdiv (dvd_zero q)

theorem constantCoeff_pctr (f : MvPowerSeries ι k) : constantCoeff (pctr S q f) = constantCoeff f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pctr, ← coeff_zero_eq_constantCoeff_apply]
  have h0 : pexpo S q 0 = 0 := by
    ext j
    simp
  rw [h0]

end PartialExpand

section Blocks3

variable {k : Type u} [CommRing k] {d : ℕ}

def blkExt₃ (c : Fin d → MvPowerSeries (Fin d) k) :
    Fin d ⊕ (Fin d ⊕ Fin d) → MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k :=
  Sum.elim (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j))
    (Sum.elim
      (fun j => subst (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j))
      (fun j => subst (fun l => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j)))

theorem blkExt₃_inl (c : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) :
    blkExt₃ c (Sum.inl j) =
      subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j) := rfl

theorem blkExt₃_inr_inl (c : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) :
    blkExt₃ c (Sum.inr (Sum.inl j)) =
      subst (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j) := rfl

theorem blkExt₃_inr_inr (c : Fin d → MvPowerSeries (Fin d) k) (j : Fin d) :
    blkExt₃ c (Sum.inr (Sum.inr j)) =
      subst (fun l => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j) := rfl

theorem hasSubst_b1 :
    HasSubst (fun l : Fin d => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_b2 :
    HasSubst (fun l : Fin d => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_b3 :
    HasSubst (fun l : Fin d => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem constantCoeff_blkExt₃ {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0)
    (s : Fin d ⊕ (Fin d ⊕ Fin d)) : (blkExt₃ c s).constantCoeff = 0 := by
  rcases s with j | j | j
  · exact constantCoeff_subst_eq_zero (hasSubst_b1 (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  · exact constantCoeff_subst_eq_zero (hasSubst_b2 (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  · exact constantCoeff_subst_eq_zero (hasSubst_b3 (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)

theorem hasSubst_blkExt₃ {c : Fin d → MvPowerSeries (Fin d) k} (hc : ∀ i, (c i).constantCoeff = 0) :
    HasSubst (blkExt₃ c) :=
  hasSubst_of_constantCoeff_zero (constantCoeff_blkExt₃ hc)

theorem hasSubst_elim₃ {τ : Type*} {a b c : Fin d → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0)
    (hc : ∀ j, (c j).constantCoeff = 0) : HasSubst (Sum.elim a (Sum.elim b c)) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j | j) <;> simp [ha, hb, hc])

theorem hasSubst_elim₂ {τ : Type*} {a b : Fin d → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) :
    HasSubst (Sum.elim a b) :=
  hasSubst_of_constantCoeff_zero (by rintro (j | j) <;> simp [ha, hb])

theorem subst_elim_blkExt₃ {τ : Type*} {a b c' : Fin d → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0)
    (hc' : ∀ j, (c' j).constantCoeff = 0) (c : Fin d → MvPowerSeries (Fin d) k)
    (s : Fin d ⊕ (Fin d ⊕ Fin d)) :
    subst (Sum.elim a (Sum.elim b c')) (blkExt₃ c s) =
      Sum.elim (fun j => subst a (c j)) (Sum.elim (fun j => subst b (c j)) (fun j => subst c' (c j))) s := by
  have habc := hasSubst_elim₃ ha hb hc'
  rcases s with j | j | j
  · show subst _ (subst _ (c j)) = subst a (c j)
    rw [subst_comp_subst_apply (hasSubst_b1 (k := k) (d := d)) habc]
    congr 1
    funext l
    exact subst_X habc (Sum.inl l)
  · show subst _ (subst _ (c j)) = subst b (c j)
    rw [subst_comp_subst_apply (hasSubst_b2 (k := k) (d := d)) habc]
    congr 1
    funext l
    exact subst_X habc (Sum.inr (Sum.inl l))
  · show subst _ (subst _ (c j)) = subst c' (c j)
    rw [subst_comp_subst_apply (hasSubst_b3 (k := k) (d := d)) habc]
    congr 1
    funext l
    exact subst_X habc (Sum.inr (Sum.inr l))

theorem subst_blkExt₃_blkExt₃ {c c' : Fin d → MvPowerSeries (Fin d) k}
    (hc : ∀ i, (c i).constantCoeff = 0) (s : Fin d ⊕ (Fin d ⊕ Fin d)) :
    subst (blkExt₃ c) (blkExt₃ c' s) = blkExt₃ (fun j => subst c (c' j)) s := by
  have hcs := hasSubst_of_constantCoeff_zero hc
  have h1 : ∀ j, (subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_b1 (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  have h2 : ∀ j, (subst (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_b2 (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  have h3 : ∀ j, (subst (fun l => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (c j)).constantCoeff = 0 :=
    fun j => constantCoeff_subst_eq_zero (hasSubst_b3 (k := k) (d := d)) (fun _ => constantCoeff_X _) (hc j)
  refine (subst_elim_blkExt₃ h1 h2 h3 c' s).trans ?_
  rcases s with j | j | j
  · show subst (fun j => subst _ (c j)) (c' j) = subst _ (subst c (c' j))
    rw [subst_comp_subst_apply hcs (hasSubst_b1 (k := k) (d := d))]
  · show subst (fun j => subst _ (c j)) (c' j) = subst _ (subst c (c' j))
    rw [subst_comp_subst_apply hcs (hasSubst_b2 (k := k) (d := d))]
  · show subst (fun j => subst _ (c j)) (c' j) = subst _ (subst c (c' j))
    rw [subst_comp_subst_apply hcs (hasSubst_b3 (k := k) (d := d))]

theorem blkExt₃_X : blkExt₃ (fun i : Fin d => (X i : MvPowerSeries (Fin d) k)) =
    fun s => (X s : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k) := by
  funext s
  rcases s with j | j | j
  · exact subst_X (hasSubst_b1 (k := k) (d := d)) j
  · exact subst_X (hasSubst_b2 (k := k) (d := d)) j
  · exact subst_X (hasSubst_b3 (k := k) (d := d)) j

theorem subst_blkExt₃_injective {α β : Fin d → MvPowerSeries (Fin d) k}
    (hα0 : ∀ i, (α i).constantCoeff = 0) (hβ0 : ∀ i, (β i).constantCoeff = 0)
    (hαβ : ∀ i, subst α (β i) = X i) :
    Function.Injective (fun g : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k => subst (blkExt₃ β) g) := by
  intro g g' hgg'
  have h := congrArg (subst (blkExt₃ α)) hgg'
  simp only at h
  rwa [subst_comp_subst_apply (hasSubst_blkExt₃ hβ0) (hasSubst_blkExt₃ hα0),
    subst_comp_subst_apply (hasSubst_blkExt₃ hβ0) (hasSubst_blkExt₃ hα0),
    funext (subst_blkExt₃_blkExt₃ hα0), funext hαβ, blkExt₃_X, subst_self] at h

end Blocks3

section Frobenius

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [CommRing k] [CharP k p]

theorem pow_p_eq_subst_X_pow {ι : Type*} (g : MvPowerSeries ι k) :
    g ^ p = subst (fun s : ι => (X s : MvPowerSeries ι k) ^ p) (MvPowerSeries.map (frobenius k p) g) := by
  haveI : ExpChar k p := ExpChar.prime hp.out
  rw [← map_frobenius_expand p hp.out.ne_zero, map_expand, MvPowerSeries.expand, substAlgHom_apply]

end Frobenius

section Construction

variable {p : ℕ} [hp : Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
  {Ψ Φ : MvFormalGroup d k}

structure NF (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] {d : ℕ}
    {Ψ Φ : MvFormalGroup d k} (ψ : Ψ.Hom Φ) where
  T : Finset (Fin d)
  Q : Matrix (Fin d) (Fin d) k
  α : Fin d → MvPowerSeries (Fin d) k
  β : Fin d → MvPowerSeries (Fin d) k
  hα0 : ∀ i, (α i).constantCoeff = 0
  hβ0 : ∀ i, (β i).constantCoeff = 0
  hαβ : ∀ i, subst α (β i) = X i
  hβα : ∀ i, subst β (α i) = X i
  hβT : ∀ i ∈ T, β i = ∑ j, Q i j • ψ.toPowerSeries j
  hKL : ∀ (i : Fin d) (m : Fin d →₀ ℕ), (∃ j ∉ T, ¬ p ∣ m j) → coeff m (subst α (ψ.toPowerSeries i)) = 0

namespace NF

set_option linter.unusedSectionVars false

variable {ψ : Ψ.Hom Φ} (D : NF p ψ)

local notation "σ" => frobenius k p

def E : Fin d → MvPowerSeries (Fin d) k := pE (fun j => j ∈ D.T) p

def R : Fin d → MvPowerSeries (Fin d) k := pE (fun j => j ∉ D.T) p

def pi : Fin d → MvPowerSeries (Fin d) k := fun j => subst D.β (D.E j)

def rho : Fin d → MvPowerSeries (Fin d) k := fun j => subst D.R (MvPowerSeries.map σ (D.α j))

def psiBar : Fin d → MvPowerSeries (Fin d) k :=
  fun i => pctr (fun j => j ∈ D.T) p (subst D.α (ψ.toPowerSeries i))

omit [CharP k p] in
theorem E_apply (j : Fin d) : D.E j = if j ∈ D.T then X j else X j ^ p := rfl

omit [CharP k p] in
theorem R_apply (j : Fin d) : D.R j = if j ∉ D.T then X j else X j ^ p := rfl

omit [CharP k p] in
theorem hE0 : ∀ j, (D.E j).constantCoeff = 0 := constantCoeff_pE hp.out.pos

omit [CharP k p] in
theorem hR0 : ∀ j, (D.R j).constantCoeff = 0 := constantCoeff_pE hp.out.pos

theorem hEs : HasSubst D.E := hasSubst_of_constantCoeff_zero D.hE0

theorem hRs : HasSubst D.R := hasSubst_of_constantCoeff_zero D.hR0

omit [CharP k p] in
theorem hαs : HasSubst D.α := hasSubst_of_constantCoeff_zero D.hα0

omit [CharP k p] in
theorem hβs : HasSubst D.β := hasSubst_of_constantCoeff_zero D.hβ0

theorem hpi0 : ∀ j, (D.pi j).constantCoeff = 0 :=
  fun j => constantCoeff_subst_eq_zero D.hβs D.hβ0 (D.hE0 j)

theorem hpis : HasSubst D.pi := hasSubst_of_constantCoeff_zero D.hpi0

theorem hασ0 : ∀ j, (MvPowerSeries.map σ (D.α j)).constantCoeff = 0 := fun j => by
  rw [constantCoeff_map, D.hα0, map_zero]

theorem hβσ0 : ∀ j, (MvPowerSeries.map σ (D.β j)).constantCoeff = 0 := fun j => by
  rw [constantCoeff_map, D.hβ0, map_zero]

theorem hrho0 : ∀ j, (D.rho j).constantCoeff = 0 :=
  fun j => constantCoeff_subst_eq_zero D.hRs D.hR0 (D.hασ0 j)

theorem hrhos : HasSubst D.rho := hasSubst_of_constantCoeff_zero D.hrho0

theorem hpsiBar0 : ∀ i, (D.psiBar i).constantCoeff = 0 := fun i => by
  rw [psiBar, constantCoeff_pctr]
  exact constantCoeff_subst_eq_zero D.hαs D.hα0 (ψ.constantCoeff_eq_zero i)

theorem hpsiBars : HasSubst D.psiBar := hasSubst_of_constantCoeff_zero D.hpsiBar0

omit [CharP k p] in

theorem subst_E_psiBar (i : Fin d) : subst D.E (D.psiBar i) = subst D.α (ψ.toPowerSeries i) := by
  refine subst_pE_pctr hp.out.pos _ fun m hm => D.hKL i m ?_
  obtain ⟨j, hj, hdiv⟩ := hm
  exact ⟨j, hj, hdiv⟩

theorem subst_pi_psiBar (i : Fin d) : subst D.pi (D.psiBar i) = ψ.toPowerSeries i := by
  show subst (fun j => subst D.β (D.E j)) (D.psiBar i) = _
  rw [← subst_comp_subst_apply D.hEs D.hβs, subst_E_psiBar, subst_comp_subst_apply D.hαs D.hβs,
    funext D.hβα]
  exact congrFun subst_self _

theorem pi_of_mem {j : Fin d} (hj : j ∈ D.T) : D.pi j = D.β j := by
  show subst D.β (D.E j) = _
  rw [E_apply, if_pos hj, subst_X D.hβs]

theorem pi_of_not_mem {j : Fin d} (hj : j ∉ D.T) : D.pi j = D.β j ^ p := by
  show subst D.β (D.E j) = _
  rw [E_apply, if_neg hj, subst_pow D.hβs, subst_X D.hβs]

theorem subst_pi_R (j : Fin d) : subst D.pi (D.R j) = D.β j ^ p := by
  rw [R_apply]
  by_cases hj : j ∈ D.T
  · rw [if_neg (not_not.mpr hj), subst_pow D.hpis, subst_X D.hpis, D.pi_of_mem hj]
  · rw [if_pos hj, subst_X D.hpis, D.pi_of_not_mem hj]

theorem subst_pi_rho (m : Fin d) : subst D.pi (D.rho m) = (X m : MvPowerSeries (Fin d) k) ^ p := by
  show subst D.pi (subst D.R (MvPowerSeries.map σ (D.α m))) = _
  rw [subst_comp_subst_apply D.hRs D.hpis]
  have hfam : (fun j => subst D.pi (D.R j)) =
      fun j => subst (fun s : Fin d => (X s : MvPowerSeries (Fin d) k) ^ p) (MvPowerSeries.map σ (D.β j)) := by
    funext j
    rw [D.subst_pi_R j, pow_p_eq_subst_X_pow]
  rw [hfam, ← subst_comp_subst_apply (hasSubst_of_constantCoeff_zero D.hβσ0) (HasSubst.X_pow hp.out.ne_zero),
    ← map_subst D.hβs, D.hβα m, map_X, subst_X (HasSubst.X_pow hp.out.ne_zero)]

theorem sum_Q_smul_psiBar {i : Fin d} (hi : i ∈ D.T) : (∑ j, D.Q i j • D.psiBar j) = X i := by
  have h1 : (∑ j, D.Q i j • D.psiBar j) =
      pctr (fun j => j ∈ D.T) p (subst D.α (∑ j, D.Q i j • ψ.toPowerSeries j)) := by
    simp only [psiBar, ← pctr_smul, ← pctr_sum, ← coe_substAlgHom D.hαs, map_sum, map_smul]
  rw [h1, ← D.hβT i hi, D.hαβ i]
  exact pctr_X_of hp.out.pos i hi

def law [Φ.IsComm] : Fin d → MvPowerSeries (Fin d ⊕ Fin d) k := fun i =>
  if i ∈ D.T then ∑ j, D.Q i j • subst (blkExt D.psiBar) (Φ.toPowerSeries j)
  else subst (blkExt D.rho) (MvPowerSeries.map σ (subst Ψ.toPowerSeries (D.β i)))

variable [Φ.IsComm]

theorem law_of_mem {i : Fin d} (hi : i ∈ D.T) :
    D.law i = ∑ j, D.Q i j • subst (blkExt D.psiBar) (Φ.toPowerSeries j) := by
  rw [law, if_pos hi]

theorem law_of_not_mem {i : Fin d} (hi : i ∉ D.T) :
    D.law i = subst (blkExt D.rho) (MvPowerSeries.map σ (subst Ψ.toPowerSeries (D.β i))) := by
  rw [law, if_neg hi]

theorem H_pi (i : Fin d) : subst Ψ.toPowerSeries (D.pi i) = subst (blkExt D.pi) (D.law i) := by
  by_cases hi : i ∈ D.T
  · rw [D.pi_of_mem hi, D.law_of_mem hi, D.hβT i hi, ← coe_substAlgHom Ψ.hasSubst_toPowerSeries, map_sum,
      ← coe_substAlgHom (hasSubst_blkExt D.hpi0), map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, map_smul, coe_substAlgHom, coe_substAlgHom, ψ.subst_eq j,
      subst_comp_subst_apply (hasSubst_blkExt D.hpsiBar0) (hasSubst_blkExt D.hpi0),
      funext (subst_blkExt_blkExt D.hpi0), funext D.subst_pi_psiBar]
    rfl
  · rw [D.pi_of_not_mem hi, D.law_of_not_mem hi, subst_pow Ψ.hasSubst_toPowerSeries, pow_p_eq_subst_X_pow,
      subst_comp_subst_apply (hasSubst_blkExt D.hrho0) (hasSubst_blkExt D.hpi0),
      funext (subst_blkExt_blkExt D.hpi0), funext D.subst_pi_rho, blkExt_X_pow]

theorem H_gen {τ : Type*} {a b : Fin d → MvPowerSeries τ k}
    (ha : ∀ j, (a j).constantCoeff = 0) (hb : ∀ j, (b j).constantCoeff = 0) (i : Fin d) :
    subst (Sum.elim (fun j => subst a (D.pi j)) (fun j => subst b (D.pi j))) (D.law i) =
      subst (fun t => subst (Sum.elim a b) (Ψ.toPowerSeries t)) (D.pi i) := by
  have hab := hasSubst_elim₂ ha hb
  have h := congrArg (subst (Sum.elim a b)) (D.H_pi i)
  rw [subst_comp_subst_apply Ψ.hasSubst_toPowerSeries hab,
    subst_comp_subst_apply (hasSubst_blkExt D.hpi0) hab] at h
  rw [h]
  congr 1
  funext s
  exact (subst_elim_blkExt (hasSubst_of_constantCoeff_zero ha) (hasSubst_of_constantCoeff_zero hb) D.pi s).symm

omit [CharP k p] in
theorem blkExt_E : blkExt D.E = pE (fun s : Fin d ⊕ Fin d => Sum.elim (fun j => j) (fun j => j) s ∈ D.T) p := by
  funext s
  rcases s with j | j
  · show subst _ (D.E j) = _
    rw [E_apply]
    unfold pE
    simp only [Sum.elim_inl]
    split_ifs
    · rw [subst_X (hasSubst_inl (k := k) (d := d))]
    · rw [subst_pow (hasSubst_inl (k := k) (d := d)), subst_X (hasSubst_inl (k := k) (d := d))]
  · show subst _ (D.E j) = _
    rw [E_apply]
    unfold pE
    simp only [Sum.elim_inr]
    split_ifs
    · rw [subst_X (hasSubst_inr (k := k) (d := d))]
    · rw [subst_pow (hasSubst_inr (k := k) (d := d)), subst_X (hasSubst_inr (k := k) (d := d))]

omit [CharP k p] in
theorem blkExt₃_E : blkExt₃ D.E = pE (fun s : Fin d ⊕ (Fin d ⊕ Fin d) =>
    Sum.elim (fun j => j) (Sum.elim (fun j => j) (fun j => j)) s ∈ D.T) p := by
  funext s
  rcases s with j | j | j
  · show subst _ (D.E j) = _
    rw [E_apply]
    unfold pE
    simp only [Sum.elim_inl]
    split_ifs
    · rw [subst_X (hasSubst_b1 (k := k) (d := d))]
    · rw [subst_pow (hasSubst_b1 (k := k) (d := d)), subst_X (hasSubst_b1 (k := k) (d := d))]
  · show subst _ (D.E j) = _
    rw [E_apply]
    unfold pE
    simp only [Sum.elim_inr, Sum.elim_inl]
    split_ifs
    · rw [subst_X (hasSubst_b2 (k := k) (d := d))]
    · rw [subst_pow (hasSubst_b2 (k := k) (d := d)), subst_X (hasSubst_b2 (k := k) (d := d))]
  · show subst _ (D.E j) = _
    rw [E_apply]
    unfold pE
    simp only [Sum.elim_inr]
    split_ifs
    · rw [subst_X (hasSubst_b3 (k := k) (d := d))]
    · rw [subst_pow (hasSubst_b3 (k := k) (d := d)), subst_X (hasSubst_b3 (k := k) (d := d))]

theorem inj₂ : Function.Injective (fun g : MvPowerSeries (Fin d ⊕ Fin d) k => subst (blkExt D.pi) g) := by
  intro g g' h
  have hcomp : ∀ f : MvPowerSeries (Fin d ⊕ Fin d) k,
      subst (blkExt D.pi) f = subst (blkExt D.β) (subst (blkExt D.E) f) := fun f => by
    show subst (blkExt fun j => subst D.β (D.E j)) f = _
    rw [subst_comp_subst_apply (hasSubst_blkExt D.hE0) (hasSubst_blkExt D.hβ0)]
    congr 1
    funext s
    exact (subst_blkExt_blkExt D.hβ0 s).symm
  simp only [hcomp] at h
  have h2 := subst_blkExt_injective D.hα0 D.hβ0 D.hαβ h
  try simp only at h2
  rw [D.blkExt_E] at h2
  exact subst_pE_injective hp.out.pos h2

theorem inj₃ : Function.Injective
    (fun g : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k => subst (blkExt₃ D.pi) g) := by
  intro g g' h
  have hcomp : ∀ f : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k,
      subst (blkExt₃ D.pi) f = subst (blkExt₃ D.β) (subst (blkExt₃ D.E) f) := fun f => by
    show subst (blkExt₃ fun j => subst D.β (D.E j)) f = _
    rw [subst_comp_subst_apply (hasSubst_blkExt₃ D.hE0) (hasSubst_blkExt₃ D.hβ0)]
    congr 1
    funext s
    exact (subst_blkExt₃_blkExt₃ D.hβ0 s).symm
  simp only [hcomp] at h
  have h2 := subst_blkExt₃_injective D.hα0 D.hβ0 D.hαβ h
  try simp only at h2
  rw [D.blkExt₃_E] at h2
  exact subst_pE_injective hp.out.pos h2

section LinCoeff

omit [CharP k p] [Φ.IsComm]

theorem coeff_inl_blkExt_inl (c : Fin d → MvPowerSeries (Fin d) k)
    (l m : Fin d) : coeff (Finsupp.single (Sum.inl l) 1) (blkExt c (Sum.inl m)) = coeff (Finsupp.single l 1) (c m) := by
  classical
  show coeff _ (subst _ (c m)) = _
  rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _)]
  simp [coeff_index_single_X]

theorem coeff_inl_blkExt_inr (c : Fin d → MvPowerSeries (Fin d) k)
    (l m : Fin d) : coeff (Finsupp.single (Sum.inl l) 1) (blkExt c (Sum.inr m)) = 0 := by
  classical
  show coeff _ (subst _ (c m)) = _
  rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _)]
  simp [coeff_index_single_X]

theorem coeff_inr_blkExt_inl (c : Fin d → MvPowerSeries (Fin d) k)
    (l m : Fin d) : coeff (Finsupp.single (Sum.inr l) 1) (blkExt c (Sum.inl m)) = 0 := by
  classical
  show coeff _ (subst _ (c m)) = _
  rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _)]
  simp [coeff_index_single_X]

theorem coeff_inr_blkExt_inr (c : Fin d → MvPowerSeries (Fin d) k)
    (l m : Fin d) : coeff (Finsupp.single (Sum.inr l) 1) (blkExt c (Sum.inr m)) = coeff (Finsupp.single l 1) (c m) := by
  classical
  show coeff _ (subst _ (c m)) = _
  rw [MvFormalGroup.coeff_single_subst (fun _ => constantCoeff_X _)]
  simp [coeff_index_single_X]

theorem coeff_inl_subst_law (F : MvFormalGroup d k) {g : Fin d → MvPowerSeries (Fin d) k}
    (_hg : ∀ i, (g i).constantCoeff = 0) (i m : Fin d) :
    coeff (Finsupp.single (Sum.inl m) 1) (subst F.toPowerSeries (g i)) = coeff (Finsupp.single m 1) (g i) := by
  classical
  rw [MvFormalGroup.coeff_single_subst F.constantCoeff_eq_zero]
  simp [F.coeff_single_inl]

theorem coeff_inr_subst_law (F : MvFormalGroup d k) {g : Fin d → MvPowerSeries (Fin d) k}
    (_hg : ∀ i, (g i).constantCoeff = 0) (i m : Fin d) :
    coeff (Finsupp.single (Sum.inr m) 1) (subst F.toPowerSeries (g i)) = coeff (Finsupp.single m 1) (g i) := by
  classical
  rw [MvFormalGroup.coeff_single_subst F.constantCoeff_eq_zero]
  simp [F.coeff_single_inr]

end LinCoeff

omit [CharP k p] [Φ.IsComm] in

theorem sum_coeff_β_mul_coeff_α (i l : Fin d) :
    (∑ m, coeff (Finsupp.single m 1) (D.β i) * coeff (Finsupp.single l 1) (D.α m)) = if i = l then 1 else 0 := by
  have h := linearPart_subst D.hα0 D.β
  rw [funext D.hαβ, linearPart_X] at h
  have h2 := congrFun (congrFun h i) l
  rw [Matrix.one_apply, Matrix.mul_apply] at h2
  rw [h2]
  rfl

omit [CharP k p] [Φ.IsComm] in
theorem sum_coeff_α_mul_coeff_β (i l : Fin d) :
    (∑ m, coeff (Finsupp.single m 1) (D.α i) * coeff (Finsupp.single l 1) (D.β m)) = if i = l then 1 else 0 := by
  have h := linearPart_subst D.hβ0 D.α
  rw [funext D.hβα, linearPart_X] at h
  have h2 := congrFun (congrFun h i) l
  rw [Matrix.one_apply, Matrix.mul_apply] at h2
  rw [h2]
  rfl

omit [Φ.IsComm] in

theorem coeff_single_R (l t : Fin d) :
    coeff (Finsupp.single l 1) (D.R t) = if t ∉ D.T then (if l = t then 1 else 0) else 0 := by
  classical
  rw [R_apply]
  by_cases ht : t ∈ D.T
  · rw [if_neg (not_not.mpr ht), if_neg (not_not.mpr ht), coeff_X_pow, if_neg]
    intro h
    have h1 := congrArg (fun m => m t) h
    simp only [Finsupp.single_apply] at h1
    split_ifs at h1 with hlt
    · exact hp.out.one_lt.ne h1
    · exact hp.out.ne_zero h1.symm
  · rw [if_pos ht, if_pos ht, coeff_index_single_X]

omit [Φ.IsComm] in

theorem coeff_single_rho (l m : Fin d) :
    coeff (Finsupp.single l 1) (D.rho m) = if l ∉ D.T then σ (coeff (Finsupp.single l 1) (D.α m)) else 0 := by
  classical
  show coeff _ (subst D.R (MvPowerSeries.map σ (D.α m))) = _
  rw [MvFormalGroup.coeff_single_subst D.hR0]
  simp_rw [coeff_map, D.coeff_single_R]
  rw [Finset.sum_eq_single l]
  · by_cases hl : l ∈ D.T
    · rw [if_neg (not_not.mpr hl), if_neg (not_not.mpr hl), mul_zero]
    · rw [if_pos hl, if_pos hl, if_pos rfl, mul_one]
  · intro t _ htl
    simp [Ne.symm htl]
  · intro h; exact absurd (Finset.mem_univ l) h

theorem constantCoeff_law (i : Fin d) : (D.law i).constantCoeff = 0 := by
  by_cases hi : i ∈ D.T
  · rw [D.law_of_mem hi, map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [smul_eq_C_mul, map_mul, constantCoeff_subst_eq_zero (hasSubst_blkExt D.hpsiBar0)
      (constantCoeff_blkExt D.hpsiBar0) (Φ.constantCoeff_eq_zero j), mul_zero]
  · rw [D.law_of_not_mem hi]
    refine constantCoeff_subst_eq_zero (hasSubst_blkExt D.hrho0) (constantCoeff_blkExt D.hrho0) ?_
    rw [constantCoeff_map, constantCoeff_subst_eq_zero Ψ.hasSubst_toPowerSeries Ψ.constantCoeff_eq_zero
      (D.hβ0 i), map_zero]

theorem hlaws : HasSubst D.law := hasSubst_of_constantCoeff_zero D.constantCoeff_law

theorem coeff_single_inl_law (i l : Fin d) :
    coeff (Finsupp.single (Sum.inl l) 1) (D.law i) = if i = l then 1 else 0 := by
  classical
  by_cases hi : i ∈ D.T
  · rw [D.law_of_mem hi, map_sum]
    have hterm : ∀ j, coeff (Finsupp.single (Sum.inl l) 1) (D.Q i j • subst (blkExt D.psiBar) (Φ.toPowerSeries j)) =
        D.Q i j * coeff (Finsupp.single l 1) (D.psiBar j) := by
      intro j
      rw [map_smul, smul_eq_mul, MvFormalGroup.coeff_single_subst (constantCoeff_blkExt D.hpsiBar0),
        Fintype.sum_sum_type]
      simp [Φ.coeff_single_inl, Φ.coeff_single_inr, coeff_inl_blkExt_inl, coeff_inl_blkExt_inr]
    simp only [hterm]
    have hsum : (∑ j, D.Q i j * coeff (Finsupp.single l 1) (D.psiBar j)) =
        coeff (Finsupp.single l 1) (∑ j, D.Q i j • D.psiBar j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    rw [hsum, D.sum_Q_smul_psiBar hi, coeff_index_single_X]
    simp only [eq_comm]
  · rw [D.law_of_not_mem hi, MvFormalGroup.coeff_single_subst (constantCoeff_blkExt D.hrho0),
      Fintype.sum_sum_type]
    simp only [coeff_map, coeff_inl_blkExt_inl, coeff_inl_blkExt_inr, mul_zero, Finset.sum_const_zero,
      add_zero, coeff_inl_subst_law Ψ D.hβ0, D.coeff_single_rho]
    by_cases hl : l ∈ D.T
    · have hil : i ≠ l := fun h => hi (h ▸ hl)
      rw [if_neg hil]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [if_neg (not_not.mpr hl), mul_zero]
    · simp only [if_pos hl, ← map_mul, ← map_sum, D.sum_coeff_β_mul_coeff_α]
      split_ifs <;> simp

theorem coeff_single_inr_law (i l : Fin d) :
    coeff (Finsupp.single (Sum.inr l) 1) (D.law i) = if i = l then 1 else 0 := by
  classical
  by_cases hi : i ∈ D.T
  · rw [D.law_of_mem hi, map_sum]
    have hterm : ∀ j, coeff (Finsupp.single (Sum.inr l) 1) (D.Q i j • subst (blkExt D.psiBar) (Φ.toPowerSeries j)) =
        D.Q i j * coeff (Finsupp.single l 1) (D.psiBar j) := by
      intro j
      rw [map_smul, smul_eq_mul, MvFormalGroup.coeff_single_subst (constantCoeff_blkExt D.hpsiBar0),
        Fintype.sum_sum_type]
      simp [Φ.coeff_single_inl, Φ.coeff_single_inr, coeff_inr_blkExt_inl, coeff_inr_blkExt_inr]
    simp only [hterm]
    have hsum : (∑ j, D.Q i j * coeff (Finsupp.single l 1) (D.psiBar j)) =
        coeff (Finsupp.single l 1) (∑ j, D.Q i j • D.psiBar j) := by
      rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
    rw [hsum, D.sum_Q_smul_psiBar hi, coeff_index_single_X]
    simp only [eq_comm]
  · rw [D.law_of_not_mem hi, MvFormalGroup.coeff_single_subst (constantCoeff_blkExt D.hrho0),
      Fintype.sum_sum_type]
    simp only [coeff_map, coeff_inr_blkExt_inl, coeff_inr_blkExt_inr, mul_zero, Finset.sum_const_zero,
      zero_add, coeff_inr_subst_law Ψ D.hβ0, D.coeff_single_rho]
    by_cases hl : l ∈ D.T
    · have hil : i ≠ l := fun h => hi (h ▸ hl)
      rw [if_neg hil]
      refine Finset.sum_eq_zero fun m _ => ?_
      rw [if_neg (not_not.mpr hl), mul_zero]
    · simp only [if_pos hl, ← map_mul, ← map_sum, D.sum_coeff_β_mul_coeff_α]
      split_ifs <;> simp

theorem assoc_law (i : Fin d) :
    subst
      (Sum.elim
        (fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
            fun l => X (Sum.inr (Sum.inl l)))
          (D.law j))
        fun j => X (Sum.inr (Sum.inr j)))
      (D.law i)
      =
    subst
      (Sum.elim
        (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
        fun j => subst
          (Sum.elim
            (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
            fun l => X (Sum.inr (Sum.inr l)))
          (D.law j))
      (D.law i) := by

  have hL12z : ∀ s : Fin d ⊕ Fin d, ((Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
      fun l => X (Sum.inr (Sum.inl l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> exact constantCoeff_X _
  have hL23z : ∀ s : Fin d ⊕ Fin d, ((Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
      fun l => X (Sum.inr (Sum.inr l))) s).constantCoeff = 0 := by
    rintro (l | l) <;> exact constantCoeff_X _
  have hL12 := hasSubst_of_constantCoeff_zero hL12z
  have hL23 := hasSubst_of_constantCoeff_zero hL23z
  have hb1z : ∀ l : Fin d, ((X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)).constantCoeff = 0 :=
    fun _ => constantCoeff_X _
  have hb2z : ∀ l : Fin d, ((X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)).constantCoeff = 0 :=
    fun _ => constantCoeff_X _
  have hb3z : ∀ l : Fin d, ((X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)).constantCoeff = 0 :=
    fun _ => constantCoeff_X _
  have ha1z : ∀ t : Fin d, (subst (Sum.elim
      (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
      fun l => X (Sum.inr (Sum.inl l))) (Ψ.toPowerSeries t)).constantCoeff = 0 :=
    fun t => constantCoeff_subst_eq_zero hL12 hL12z (Ψ.constantCoeff_eq_zero t)
  have ha2z : ∀ t : Fin d, (subst (Sum.elim
      (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
      fun l => X (Sum.inr (Sum.inr l))) (Ψ.toPowerSeries t)).constantCoeff = 0 :=
    fun t => constantCoeff_subst_eq_zero hL23 hL23z (Ψ.constantCoeff_eq_zero t)
  have hB3 := hasSubst_blkExt₃ D.hpi0
  apply D.inj₃
  simp only

  have hFL : HasSubst (Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
        fun l => X (Sum.inr (Sum.inl l))) (D.law j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) :=
    hasSubst_elim₂ (fun j => constantCoeff_subst_eq_zero hL12 hL12z (D.constantCoeff_law j)) hb3z
  have hFR : HasSubst (Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
        fun l => X (Sum.inr (Sum.inr l))) (D.law j)) :=
    hasSubst_elim₂ hb1z (fun j => constantCoeff_subst_eq_zero hL23 hL23z (D.constantCoeff_law j))
  rw [subst_comp_subst_apply hFL hB3, subst_comp_subst_apply hFR hB3]

  have hfamL : (fun s => subst (blkExt₃ D.pi) ((Sum.elim
      (fun j => subst (Sum.elim
        (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
        fun l => X (Sum.inr (Sum.inl l))) (D.law j))
      fun j => (X (Sum.inr (Sum.inr j)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) s)) =
      Sum.elim
        (fun j => subst (fun t => subst (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
          fun l => X (Sum.inr (Sum.inl l))) (Ψ.toPowerSeries t)) (D.pi j))
        (fun j => subst (fun l => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
          (D.pi j)) := by
    funext s
    rcases s with j | j
    · show subst (blkExt₃ D.pi) (subst _ (D.law j)) = _
      rw [subst_comp_subst_apply hL12 hB3]
      have hin : (fun t => subst (blkExt₃ D.pi) ((Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
          fun l => X (Sum.inr (Sum.inl l))) t)) =
          Sum.elim (fun m => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (D.pi m))
            (fun m => subst (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
              (D.pi m)) := by
        funext t
        rcases t with m | m
        · show subst (blkExt₃ D.pi) (X (Sum.inl m)) = _
          rw [subst_X hB3, blkExt₃_inl, Sum.elim_inl]
        · show subst (blkExt₃ D.pi) (X (Sum.inr (Sum.inl m))) = _
          rw [subst_X hB3, blkExt₃_inr_inl, Sum.elim_inr]
      rw [hin, D.H_gen hb1z hb2z, Sum.elim_inl]
    · show subst (blkExt₃ D.pi) (X (Sum.inr (Sum.inr j))) = _
      rw [subst_X hB3, blkExt₃_inr_inr, Sum.elim_inr]

  have hfamR : (fun s => subst (blkExt₃ D.pi) ((Sum.elim
      (fun j => (X (Sum.inl j) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
      fun j => subst (Sum.elim
        (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
        fun l => X (Sum.inr (Sum.inr l))) (D.law j)) s)) =
      Sum.elim
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k)) (D.pi j))
        (fun j => subst (fun t => subst (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
          fun l => X (Sum.inr (Sum.inr l))) (Ψ.toPowerSeries t)) (D.pi j)) := by
    funext s
    rcases s with j | j
    · show subst (blkExt₃ D.pi) (X (Sum.inl j)) = _
      rw [subst_X hB3, blkExt₃_inl, Sum.elim_inl]
    · show subst (blkExt₃ D.pi) (subst _ (D.law j)) = _
      rw [subst_comp_subst_apply hL23 hB3]
      have hin : (fun t => subst (blkExt₃ D.pi) ((Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
          fun l => X (Sum.inr (Sum.inr l))) t)) =
          Sum.elim (fun m => subst (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
              (D.pi m))
            (fun m => subst (fun l => (X (Sum.inr (Sum.inr l)) : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) k))
              (D.pi m)) := by
        funext t
        rcases t with m | m
        · show subst (blkExt₃ D.pi) (X (Sum.inr (Sum.inl m))) = _
          rw [subst_X hB3, blkExt₃_inr_inl, Sum.elim_inl]
        · show subst (blkExt₃ D.pi) (X (Sum.inr (Sum.inr m))) = _
          rw [subst_X hB3, blkExt₃_inr_inr, Sum.elim_inr]
      rw [hin, D.H_gen hb2z hb3z, Sum.elim_inr]
  rw [hfamL, hfamR, D.H_gen ha1z hb3z, D.H_gen hb1z ha2z]
  congr 1
  funext t
  exact Ψ.assoc t

theorem comm_law [Ψ.IsComm] (i : Fin d) :
    subst (Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k)) fun j => X (Sum.inl j))
      (D.law i) = D.law i := by
  have hswz : ∀ s : Fin d ⊕ Fin d, ((Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k))
      fun j => X (Sum.inl j)) s).constantCoeff = 0 := by
    rintro (j | j) <;> exact constantCoeff_X _
  have hsw := hasSubst_of_constantCoeff_zero hswz
  have hB := hasSubst_blkExt D.hpi0
  have hinrz : ∀ l : Fin d, ((X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)).constantCoeff = 0 :=
    fun _ => constantCoeff_X _
  have hinlz : ∀ l : Fin d, ((X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)).constantCoeff = 0 :=
    fun _ => constantCoeff_X _
  apply D.inj₂
  simp only
  rw [subst_comp_subst_apply hsw hB]
  have hfam : (fun s => subst (blkExt D.pi) ((Sum.elim (fun j => (X (Sum.inr j) : MvPowerSeries (Fin d ⊕ Fin d) k))
      fun j => X (Sum.inl j)) s)) =
      Sum.elim (fun j => subst (fun l => (X (Sum.inr l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (D.pi j))
        (fun j => subst (fun l => (X (Sum.inl l) : MvPowerSeries (Fin d ⊕ Fin d) k)) (D.pi j)) := by
    funext s
    rcases s with j | j
    · show subst (blkExt D.pi) (X (Sum.inr j)) = _
      rw [subst_X hB, blkExt_inr, Sum.elim_inl]
    · show subst (blkExt D.pi) (X (Sum.inl j)) = _
      rw [subst_X hB, blkExt_inl, Sum.elim_inr]
  rw [hfam, D.H_gen hinrz hinlz, ← D.H_pi i]
  congr 1
  funext t
  exact MvFormalGroup.IsComm.comm t

def quot : MvFormalGroup d k where
  toPowerSeries := D.law
  constantCoeff_eq_zero := D.constantCoeff_law
  coeff_single_inl := D.coeff_single_inl_law
  coeff_single_inr := D.coeff_single_inr_law
  assoc := D.assoc_law

scoped instance quot_isComm [Ψ.IsComm] : D.quot.IsComm := ⟨D.comm_law⟩

def piHom : Ψ.Hom D.quot where
  toPowerSeries := D.pi
  constantCoeff_eq_zero := D.hpi0
  subst_eq := D.H_pi

def rhoHom : D.quot.Hom (Ψ.map σ) where
  toPowerSeries := D.rho
  constantCoeff_eq_zero := D.hrho0
  subst_eq := by
    intro m
    have hB := hasSubst_blkExt D.hpi0
    apply D.inj₂
    show subst (blkExt D.pi) (subst D.law (D.rho m)) =
      subst (blkExt D.pi) (subst (blkExt D.rho) (MvPowerSeries.map σ (Ψ.toPowerSeries m)))
    rw [subst_comp_subst_apply D.hlaws hB, subst_comp_subst_apply (hasSubst_blkExt D.hrho0) hB,
      funext (subst_blkExt_blkExt D.hpi0), funext D.subst_pi_rho, blkExt_X_pow, ← pow_p_eq_subst_X_pow]
    have hfam : (fun i => subst (blkExt D.pi) (D.law i)) = fun i => subst Ψ.toPowerSeries (D.pi i) :=
      funext fun i => (D.H_pi i).symm
    rw [hfam, ← subst_comp_subst_apply D.hpis Ψ.hasSubst_toPowerSeries, D.subst_pi_rho,
      subst_pow Ψ.hasSubst_toPowerSeries, subst_X Ψ.hasSubst_toPowerSeries]

def psiHom : D.quot.Hom Φ where
  toPowerSeries := D.psiBar
  constantCoeff_eq_zero := D.hpsiBar0
  subst_eq := by
    intro i
    have hB := hasSubst_blkExt D.hpi0
    apply D.inj₂
    show subst (blkExt D.pi) (subst D.law (D.psiBar i)) =
      subst (blkExt D.pi) (subst (blkExt D.psiBar) (Φ.toPowerSeries i))
    rw [subst_comp_subst_apply D.hlaws hB, subst_comp_subst_apply (hasSubst_blkExt D.hpsiBar0) hB,
      funext (subst_blkExt_blkExt D.hpi0), funext D.subst_pi_psiBar]
    have hfam : (fun i => subst (blkExt D.pi) (D.law i)) = fun i => subst Ψ.toPowerSeries (D.pi i) :=
      funext fun i => (D.H_pi i).symm
    rw [hfam, ← subst_comp_subst_apply D.hpis Ψ.hasSubst_toPowerSeries, D.subst_pi_psiBar]
    exact ψ.subst_eq i

theorem psiHom_comp_piHom (i : Fin d) : (D.psiHom.comp D.piHom).toPowerSeries i = ψ.toPowerSeries i :=
  D.subst_pi_psiBar i

theorem rhoHom_comp_piHom (i : Fin d) :
    (D.rhoHom.comp D.piHom).toPowerSeries i = (X i : MvPowerSeries (Fin d) k) ^ p :=
  D.subst_pi_rho i

section Degrees

omit [Φ.IsComm]

local notation "A" => MvPowerSeries (Fin d) k

omit [CharP k p] in

theorem linearPart_α_mul_β : linearPart D.α * linearPart D.β = 1 := by
  have h := linearPart_subst D.hβ0 D.α
  rw [funext D.hβα, linearPart_X] at h
  exact h.symm

omit [CharP k p] in
theorem linearPart_β_mul_α : linearPart D.β * linearPart D.α = 1 := by
  have h := linearPart_subst D.hα0 D.β
  rw [funext D.hαβ, linearPart_X] at h
  exact h.symm

theorem isUnit_det_linearPart_α_map : IsUnit ((linearPart D.α).map σ).det := by
  have h1 : IsUnit (linearPart D.α).det := by
    refine IsUnit.of_mul_eq_one (linearPart D.β).det ?_
    rw [← Matrix.det_mul, D.linearPart_α_mul_β, Matrix.det_one]
  have h2 := h1.map σ
  rwa [RingHom.map_det, RingHom.mapMatrix_apply] at h2

theorem linearPart_rho : linearPart D.rho =
    (linearPart D.α).map σ * Matrix.diagonal (fun t => if t ∉ D.T then (1 : k) else 0) := by
  classical
  have h := linearPart_subst D.hR0 (fun m => MvPowerSeries.map σ (D.α m))
  have hR : linearPart D.R = Matrix.diagonal (fun t => if t ∉ D.T then (1 : k) else 0) := by
    ext t l
    rw [linearPart, Matrix.of_apply, D.coeff_single_R, Matrix.diagonal_apply]
    by_cases ht : t ∈ D.T
    · simp [ht]
    · by_cases htl : t = l
      · subst htl; simp [ht]
      · simp [ht, htl, Ne.symm htl]
  have hα : linearPart (fun m => MvPowerSeries.map σ (D.α m)) = (linearPart D.α).map σ := by
    ext m l
    simp [linearPart, coeff_map]
  rw [hR, hα] at h
  exact h

theorem rank_linearPart_rho : (linearPart D.rho).rank = d - D.T.card := by
  classical
  rw [D.linearPart_rho, Matrix.rank_mul_eq_right_of_isUnit_det _ _ D.isUnit_det_linearPart_α_map,
    Matrix.rank_diagonal]
  have h1 : Fintype.card {t : Fin d // (if t ∉ D.T then (1 : k) else 0) ≠ 0} = Fintype.card {t : Fin d // t ∉ D.T} :=
    Fintype.card_congr (Equiv.subtypeEquivRight fun t => by
      by_cases ht : t ∈ D.T <;> simp [ht])
  rw [h1, Fintype.card_subtype_compl, Fintype.card_fin]
  congr 1
  exact Fintype.card_coe D.T

def eβ : (MvPowerSeries (Fin d) k) ≃ₐ[k] MvPowerSeries (Fin d) k :=
  AlgEquiv.ofAlgHom (substAlgHom D.hβs) (substAlgHom D.hαs)
    (by
      apply AlgHom.ext
      intro f
      rw [AlgHom.comp_apply, substAlgHom_apply, substAlgHom_apply, AlgHom.id_apply,
        subst_comp_subst_apply D.hαs D.hβs, funext D.hβα]
      exact congrFun subst_self f)
    (by
      apply AlgHom.ext
      intro f
      rw [AlgHom.comp_apply, substAlgHom_apply, substAlgHom_apply, AlgHom.id_apply,
        subst_comp_subst_apply D.hβs D.hαs, funext D.hαβ]
      exact congrFun subst_self f)

theorem eβ_apply (f : A) : D.eβ f = subst D.β f := by
  show substAlgHom D.hβs f = _
  rw [substAlgHom_apply]

theorem coe_eβ_apply (f : A) : (D.eβ : A →+* A) f = subst D.β f := D.eβ_apply f

theorem span_pi_eq_map : Ideal.span (Set.range D.pi) = (Ideal.span (Set.range D.E)).map (D.eβ : A →+* A) := by
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨D.E j, ⟨j, rfl⟩, D.coe_eβ_apply _⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, (D.coe_eβ_apply _).symm⟩

def ccAlgHom : (MvPowerSeries (Fin d) k) →ₐ[k] k :=
  { (MvPowerSeries.constantCoeff : A →+* k) with
    commutes' := fun r => by
      show MvPowerSeries.constantCoeff (algebraMap k A r) = r
      rw [MvPowerSeries.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, constantCoeff_C] }

theorem ker_ccAlgHom : RingHom.ker (ccAlgHom (k := k) (d := d)) = Ideal.span (Set.range (X : Fin d → A)) := by
  rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff]
  ext x
  rw [RingHom.mem_ker, RingHom.mem_ker]
  rfl

def quotSpanXEquiv : (A ⧸ Ideal.span (Set.range (X : Fin d → A))) ≃ₐ[k] k :=
  (Ideal.quotientEquivAlgOfEq k (ker_ccAlgHom (k := k) (d := d)).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (f := ccAlgHom (k := k) (d := d)) fun a => ⟨C a, constantCoeff_C a⟩)

theorem finrank_quotient_span_X : Module.finrank k (A ⧸ Ideal.span (Set.range (X : Fin d → A))) = 1 := by
  rw [(quotSpanXEquiv (k := k) (d := d)).toLinearEquiv.finrank_eq, Module.finrank_self]

theorem finite_quotient_span_X : Module.Finite k (A ⧸ Ideal.span (Set.range (X : Fin d → A))) :=
  Module.Finite.equiv (quotSpanXEquiv (k := k) (d := d)).symm.toLinearEquiv

theorem finrank_quotient_span_pi :
    Module.finrank k (A ⧸ Ideal.span (Set.range D.pi)) = p ^ (d - D.T.card) := by
  have hc := (MvPowerSeries.finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq D.T p hp.out.pos
    (fun i => (X i : A)) (fun i => constantCoeff_X i)).2
  have hfam : (fun i => subst (fun j => if j ∈ D.T then (X j : A) else X j ^ p) (X i : A)) = D.E :=
    funext fun i => subst_X D.hEs i
  rw [hfam, finrank_quotient_span_X, mul_one] at hc
  rw [← hc]
  exact ((Ideal.quotientEquivAlg _ _ D.eβ D.span_pi_eq_map).toLinearEquiv.finrank_eq).symm

theorem span_range_eq_span_X {a b : Fin d → A} (ha0 : ∀ i, (a i).constantCoeff = 0)
    (hb0 : ∀ i, (b i).constantCoeff = 0) (hab : ∀ i, subst a (b i) = X i) :
    Ideal.span (Set.range a) = Ideal.span (Set.range (X : Fin d → A)) := by
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, MvPowerSeries.span_range_X_eq_ker_constantCoeff]
    exact ha0 i
  · rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    have hbi : b i ∈ Ideal.span (Set.range (X : Fin d → A)) := by
      rw [MvPowerSeries.span_range_X_eq_ker_constantCoeff]
      exact hb0 i
    have h := Ideal.mem_map_of_mem (substAlgHom (hasSubst_of_constantCoeff_zero ha0)) hbi
    rw [Ideal.map_span, substAlgHom_apply, hab i] at h
    rw [SetLike.mem_coe]
    refine Ideal.span_mono ?_ h
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by rw [substAlgHom_apply, subst_X (hasSubst_of_constantCoeff_zero ha0)]⟩

theorem span_rho_eq : Ideal.span (Set.range D.rho) = Ideal.span (Set.range D.R) := by
  have hασ := hasSubst_of_constantCoeff_zero D.hασ0
  have hinv : ∀ i, subst (fun m => MvPowerSeries.map σ (D.α m)) (MvPowerSeries.map σ (D.β i)) = X i := by
    intro i
    rw [← map_subst D.hαs, D.hαβ i, map_X]
  have h1 : Ideal.span (Set.range D.rho) =
      (Ideal.span (Set.range fun m => MvPowerSeries.map σ (D.α m))).map (substAlgHom D.hRs) := by
    rw [Ideal.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨_, ⟨j, rfl⟩, by rw [substAlgHom_apply]; rfl⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j, by rw [substAlgHom_apply]; rfl⟩
  rw [h1, span_range_eq_span_X D.hασ0 D.hβσ0 hinv, Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by rw [substAlgHom_apply, subst_X D.hRs]⟩
  · rintro ⟨j, rfl⟩
    exact ⟨X j, ⟨j, rfl⟩, by rw [substAlgHom_apply, subst_X D.hRs]⟩

theorem finite_quotient_span_rho : Module.Finite k (A ⧸ Ideal.span (Set.range D.rho)) := by
  haveI := finite_quotient_span_X (k := k) (d := d)
  have hc := (MvPowerSeries.finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq D.Tᶜ p hp.out.pos
    (fun i => (X i : A)) (fun i => constantCoeff_X i)).1.mpr inferInstance
  have hfam : (fun i => subst (fun j => if j ∈ D.Tᶜ then (X j : A) else X j ^ p) (X i : A)) = D.R := by
    have hR : (fun j => if j ∈ D.Tᶜ then (X j : A) else X j ^ p) = D.R := by
      funext j
      simp only [Finset.mem_compl, NF.R, pE]
    rw [hR]
    exact funext fun i => subst_X D.hRs i
  rw [hfam] at hc
  rw [D.span_rho_eq]
  exact hc

theorem span_ψ_eq_map : Ideal.span (Set.range ψ.toPowerSeries) =
    (Ideal.span (Set.range fun i => subst D.E (D.psiBar i))).map (D.eβ : A →+* A) := by
  have hcomp : ∀ i, subst D.β (subst D.E (D.psiBar i)) = ψ.toPowerSeries i := by
    intro i
    rw [subst_comp_subst_apply D.hEs D.hβs]
    exact D.subst_pi_psiBar i
  rw [Ideal.map_span]
  congr 1
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, by rw [D.coe_eβ_apply, hcomp]⟩
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by rw [D.coe_eβ_apply, hcomp]⟩

theorem finite_and_finrank_psiBar
    (hfin : Module.Finite k (A ⧸ Ideal.span (Set.range ψ.toPowerSeries))) :
    Module.Finite k (A ⧸ Ideal.span (Set.range D.psiBar)) ∧
    Module.finrank k (A ⧸ Ideal.span (Set.range ψ.toPowerSeries)) =
      p ^ (d - D.T.card) * Module.finrank k (A ⧸ Ideal.span (Set.range D.psiBar)) := by
  have hc := MvPowerSeries.finite_and_finrank_quotient_span_range_subst_ite_X_pow_eq D.T p hp.out.pos
    D.psiBar D.hpsiBar0
  change (Module.Finite k (A ⧸ Ideal.span (Set.range fun i => subst D.E (D.psiBar i))) ↔ _) ∧
    Module.finrank k (A ⧸ Ideal.span (Set.range fun i => subst D.E (D.psiBar i))) = _ at hc
  let e := Ideal.quotientEquivAlg _ _ D.eβ D.span_ψ_eq_map
  haveI : Module.Finite k (A ⧸ Ideal.span (Set.range fun i => subst D.E (D.psiBar i))) :=
    Module.Finite.equiv e.symm.toLinearEquiv
  refine ⟨hc.1.mp inferInstance, ?_⟩
  rw [← e.toLinearEquiv.finrank_eq, hc.2]

end Degrees

end NF
p2m_reactivate "P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.P2mKcPartialFrobQuot.NF"

end Construction
p2m_reactivate "P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.P2mKcPartialFrobQuot.NF"

end P2mKcPartialFrobQuot
p2m_reactivate "P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.P2mKcPartialFrobQuot.NF P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.P2mKcPartialFrobQuot"

open P2mKcPartialFrobQuot MvPowerSeries in

theorem solution
    (p : ℕ) [Fact p.Prime] {k : Type u} [Field k] [CharP k p] {d : ℕ}
    (Ψ Φ : MvFormalGroup d k) [Ψ.IsComm] [Φ.IsComm] (ψ : Ψ.Hom Φ)
    (hfin : Module.Finite k
      (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries))) :
    ∃ (Ψ' : MvFormalGroup d k) (_ : Ψ'.IsComm) (π : Ψ.Hom Ψ')
      (ρ : Ψ'.Hom (Ψ.map (frobenius k p))) (ψ' : Ψ'.Hom Φ),
      (∀ i, (ψ'.comp π).toPowerSeries i = ψ.toPowerSeries i) ∧
      (∀ i, (ρ.comp π).toPowerSeries i = (X i : MvPowerSeries (Fin d) k) ^ p) ∧
      (MvFormalGroup.linearPart ρ.toPowerSeries).rank =
        d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank ∧
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range π.toPowerSeries)) =
        p ^ (d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank) ∧
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ρ.toPowerSeries)) ∧
      Module.Finite k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) ∧
      Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ.toPowerSeries)) =
        p ^ (d - (MvFormalGroup.linearPart ψ.toPowerSeries).rank) *
          Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range ψ'.toPowerSeries)) := by
  obtain ⟨T, Q, α, β, hcard, -, hα0, hβ0, hαβ, hβα, hβT, hKL⟩ :=
    MvFormalGroup.Hom.exists_subst_eq_X_and_coeff_subst_eq_zero_of_not_dvd p Ψ Φ ψ
  let D : NF p ψ := ⟨T, Q, α, β, hα0, hβ0, hαβ, hβα, hβT, hKL⟩
  obtain ⟨hfin', hmul⟩ := D.finite_and_finrank_psiBar hfin
  refine ⟨D.quot, D.quot_isComm, D.piHom, D.rhoHom, D.psiHom, D.psiHom_comp_piHom, D.rhoHom_comp_piHom,
    ?_, ?_, D.finite_quotient_span_rho, hfin', ?_⟩
  · show (MvFormalGroup.linearPart D.rho).rank = _
    rw [D.rank_linearPart_rho, hcard]
  · show Module.finrank k (MvPowerSeries (Fin d) k ⧸ Ideal.span (Set.range D.pi)) = _
    rw [D.finrank_quotient_span_pi, hcard]
  · rw [← hcard]
    exact hmul

end
p2m_reactivate "P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.P2mKcPartialFrobQuot.NF P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul.P2mKcPartialFrobQuot"

end S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul
end P2MW
export P2MW.S_MvFormalGroup_Hom_exists_comp_eq_and_comp_eq_X_pow_and_finrank_eq_pow_mul (solution)
