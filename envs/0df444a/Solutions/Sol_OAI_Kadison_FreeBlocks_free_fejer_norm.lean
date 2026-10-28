-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.free_fejer_norm
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T11:01:22.020638+00:00
-- url     : https://prove2.me/submissions/5681bbfc-f8cb-41e5-a443-d23844403974

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_DihedralCorner_fejerCorner_centered
import Theorems.Thm_OAI_Kadison_DihedralCorner_fejerCorner_preGNS_norm

section
-- module Solutions.OAIQ039_CM.Commutator_HankelAlgebra
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))

include h1 htr in
theorem free_of_different_endpoints
    (hcyc : ∀ (a b : Letter S τ) (m : List (Letter S τ)),
      Reduced (a :: m ++ [b]) → a.color≠b.color → τ (word (a :: m ++ [b]))=0) :
    Free S τ := by
  intro w
  induction hn : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
    intro hw hne
    cases w with
    | nil => exact (hne rfl).elim
    | cons a w =>
      cases w using List.reverseRecOn with
      | nil => simpa using a.centered
      | append_singleton m b =>
        by_cases hab : a.color=b.color
        · have hmne : m≠[] := by
            intro hm
            subst m
            exact hw.rel hab
          have hm : Reduced m := hw.tail.left_of_append
          have ham : Reduced (a::m) :=
            (show Reduced ((a::m)++[b]) from hw).left_of_append
          let c : Letter S τ := {
            color := a.color
            val := b.val*a.val - τ (b.val*a.val) • 1
            mem := sub_mem (mul_mem (by simpa [hab] using b.mem) a.mem)
              (SMulMemClass.smul_mem _ (one_mem _))
            centered := by simp [map_sub, map_smul, h1] }
          have hc : Reduced (c::m) := by
            apply ham.imp_head
            intro z hz
            exact hz
          have hc0 : τ (word (c::m)) = 0 :=
            ih _ (by simp at hn ⊢; omega) (c::m) rfl hc (by simp)
          have hm0 : τ (word m)=0 := ih _ (by simp at hn ⊢; omega) m rfl hm hmne
          have heq : word (c::m) = b.val*a.val*word m - τ (b.val*a.val) • word m := by
            simp [word_cons, c, sub_mul]
          rw [heq, map_sub, map_smul, hm0, smul_zero, sub_zero] at hc0
          rw [word_cons, word_append, word_cons, word_nil, mul_one]
          calc
            τ (a.val * (word m*b.val)) = τ (b.val*(a.val*word m)) := by
              rw [←mul_assoc, htr]
            _ = 0 := by simpa only [mul_assoc] using hc0
        · exact hcyc a b m hw hab

end Kadison.FreeMoments

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

lemma paired_reduced (s : Letter S τ) (v : List (Letter S τ))
    (h : ∀ a∈v, a.color≠s.color) : Reduced (s::paired s v) := by
  induction v with
  | nil => exact List.IsChain.singleton _
  | cons a v ih =>
    apply List.isChain_cons_cons.mpr
    refine ⟨(h a (by simp)).symm, ?_⟩
    apply List.isChain_cons_cons.mpr
    exact ⟨h a (by simp), ih (fun b hb => h b (by simp [hb]))⟩

lemma paired_moment (hfree : Free S τ) (s : Letter S τ) (v : List (Letter S τ))
    (hne : v≠[]) (h : ∀ a∈v, a.color≠s.color) : τ (word (paired s v))=0 := by
  apply hfree _ (paired_reduced s v h).tail
  cases v with
  | nil => exact (hne rfl).elim
  | cons a v => simp

lemma word_dihedralBlocks (s d : Letter S τ) (v : List (Letter S τ × ℕ)) :
    word (paired s (dihedralBlocks d v)) =
      (v.map (fun x => x.1.val*s.val*(d.val*s.val)^x.2)).prod := by
  induction v with
  | nil => simp [dihedralBlocks]
  | cons x v ih =>
    simp only [dihedralBlocks, List.flatMap_cons, List.cons_append, paired_cons,
      paired_append, word_cons, word_append, word_paired_replicate,
      List.map_cons, List.prod_cons] at *
    rw [ih]
    simp only [mul_assoc]

theorem dihedral_cyclic_moment (hfree : Free S τ) (s d : Letter S τ)
    (hsd : d.color≠s.color) (v : List (Letter S τ × ℕ)) (hne : v≠[])
    (hcolor : ∀ x∈v, x.1.color≠s.color)
    (hd : ∀ x∈v, x.1.val*d.val=x.1.val) :
    τ ((v.map (fun x => x.1.val*(d.val*s.val)^(x.2+1))).prod)=0 := by
  have hblocks : ∀ a∈dihedralBlocks d v, a.color≠s.color := by
    intro a ha
    obtain ⟨x,hx,ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.mem_replicate] at ha
    rcases ha with rfl | ⟨_,rfl⟩
    · exact hcolor x hx
    · exact hsd
  have hbne : dihedralBlocks d v≠[] := by
    cases v with
    | nil => exact (hne rfl).elim
    | cons x v => simp [dihedralBlocks]
  have hm := paired_moment hfree s (dihedralBlocks d v) hbne hblocks
  rw [word_dihedralBlocks] at hm
  convert hm using 2
  all_goals try with_reducible_and_instances rfl
  apply congrArg List.prod
  apply List.map_congr_left
  intro x hx
  rw [pow_succ', ←mul_assoc, ←mul_assoc, hd x hx]

end Kadison.FreeMoments

namespace Kadison.CornerMoments

variable {A : Type*} [Ring A] [Algebra ℂ A]

variable (p : A)

omit [Algebra ℂ A] in
lemma left_support_prod (v : List (A×A)) (hne : v≠[])
    (h : ∀ x∈v, p*x.1=x.1) :
    p * (v.map (fun x => x.1*x.2)).prod = (v.map (fun x => x.1*x.2)).prod := by
  cases v with
  | nil => exact (hne rfl).elim
  | cons x v => simp only [List.map_cons, List.prod_cons, ←mul_assoc, h x (by simp)]

omit [Algebra ℂ A] in
lemma compressed_prod (v : List (A×A)) (hne : v≠[])
    (h : ∀ x∈v, p*x.1=x.1) :
    (v.map (fun x => x.1*x.2*p)).prod = (v.map (fun x => x.1*x.2)).prod*p := by
  induction v with
  | nil => exact (hne rfl).elim
  | cons x v ih =>
    by_cases hv : v=[]
    · subst v; simp
    · have ht : ∀ y∈v, p*y.1=y.1 := fun y hy => h y (by simp [hy])
      simp only [List.map_cons, List.prod_cons]
      rw [ih hv ht]
      simp only [mul_assoc]
      rw [←mul_assoc p, left_support_prod p v hv ht]

lemma traceremove (τ : A →ₗ[ℂ] ℂ) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
    (v : List (A×A)) (hne : v≠[]) (h : ∀ x∈v, p*x.1=x.1) :
    τ ((v.map (fun x => x.1*x.2*p)).prod)=τ ((v.map (fun x => x.1*x.2)).prod) := by
  rw [compressed_prod p v hne h, htr, left_support_prod p v hne h]

end Kadison.CornerMoments

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A)

variable (hr : MulAut.conj d u=u⁻¹)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2 : ℂ) • (1+(d : A)))

variable (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include hr hpd hdp in
lemma cosine_neg (n : ℤ) : cosine u hp (-n)=cosine u hp n := by
  apply Subtype.ext
  change p*wave u (-n)*p=p*wave u n*p
  calc
    p*wave u (-n)*p = p*wave u (-n)*((d : A)*p) := by rw [hdp]
    _ = p*((d : A)*wave u n)*p := by rw [reflection_wave u d hr n]; noncomm_ring
    _ = p*wave u n*p := by rw [←mul_assoc p, hpd]

end Kadison.DihedralCorner

namespace Kadison.DihedralCorner

open scoped ComplexOrder

variable {A : Type*} [CStarAlgebra A]

variable (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include hr hpd hdp in
lemma cosine_nonzero_mem_positive {n : ℤ} (hn : n≠0) :
    cosine u hp n∈Submodule.span ℂ (positiveCosines u hp) := by
  by_cases hpos : 0<n
  · obtain ⟨m,hm⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hm0 : 0 < m := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm0)
    subst n
    exact Submodule.subset_span ⟨k,by simp⟩
  · have hpos : 0< -n := by omega
    obtain ⟨m,hm⟩ := Int.eq_ofNat_of_zero_le hpos.le
    have hm0 : 0 < m := by omega
    obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm0)
    have heq : cosine u hp n=cosine u hp (k+1) := by
      rw [←cosine_neg u d hr hp hpd hdp n, hm]
      simp
    rw [heq]
    exact Submodule.subset_span ⟨k,rfl⟩

include hr hpd hdp in
lemma center_cosineSpace (τ : Corner hp →ₗ[ℂ] ℂ) (hτ1 : τ 1=1)
    (hτ0 : ∀ n : ℤ, n≠0 → τ (cosine u hp n)=0)
    {a : Corner hp} (ha : a∈cosineSpace u hp) :
    a-τ a • 1∈Submodule.span ℂ (positiveCosines u hp) := by
  induction ha using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨n,rfl⟩ := ha
    by_cases hn : n=0
    · subst n; simp [hτ1]
    · rw [hτ0 n hn, zero_smul, sub_zero]
      exact cosine_nonzero_mem_positive u d hr hp hpd hdp hn
  | zero => simp
  | add a b _ _ ha hb =>
    simpa only [map_add, add_smul, add_sub_add_comm] using
      (Submodule.span ℂ (positiveCosines u hp)).add_mem ha hb
  | smul z a _ ha =>
    simpa only [map_smul, smul_eq_mul, mul_smul, smul_sub] using
      (Submodule.span ℂ (positiveCosines u hp)).smul_mem z ha

include hr hpform hpd hdp in
lemma centered_cosineAlgebra_span (τ : Corner hp →ₗ[ℂ] ℂ) (hτ1 : τ 1=1)
    (hτ0 : ∀ n : ℤ, n≠0 → τ (cosine u hp n)=0)
    {a : Corner hp} (ha : a∈cosineAlgebra u d hr hp hpform hdp) (ha0 : τ a=0) :
    a∈Submodule.span ℂ (positiveCosines u hp) := by
  simpa only [ha0, zero_smul, sub_zero] using
    center_cosineSpace u d hr hp hpd hdp τ hτ1 hτ0 ha

end Kadison.DihedralCorner

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

lemma alternating_power_centered (hfree : Free S τ) (d s : Letter S τ)
    (hds : d.color≠s.color) (n : ℕ) : τ ((d.val*s.val)^(n+1))=0 := by
  have h := paired_moment hfree s (List.replicate (n+1) d) (by simp)
    (by intro a ha; simpa only [List.mem_replicate] using (show a.color≠s.color from by
      obtain ⟨_,rfl⟩ := List.mem_replicate.mp ha; exact hds))
  rwa [word_paired_replicate] at h

lemma alternating_odd_centered (hfree : Free S τ) (d s : Letter S τ)
    (hds : d.color≠s.color) (n : ℕ) : τ (s.val*(d.val*s.val)^n)=0 := by
  have h := hfree (s::paired s (List.replicate n d))
    (paired_reduced s (List.replicate n d) (by
      intro a ha; obtain ⟨_,rfl⟩ := List.mem_replicate.mp ha; exact hds)) (by simp)
  rwa [word_cons, word_paired_replicate] at h

end Kadison.FreeMoments

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (htr : ∀ a b : A, τ (a*b)=τ (b*a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hd2 : (d : A)*(d : A)=1)

include htr hfree hij hd hs hd0 hs0 hpform hd2 in
lemma cosine_positive_centered (n : ℕ) : τ ((cosine (d*s) hp (n+1) : Corner hp) : A)=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have hpow := alternating_power_centered hfree D F hij n
  have hodd := alternating_odd_centered hfree D F hij n
  change τ (((d : A)*(s : A))^(n+1))=0 at hpow
  change τ ((s : A)*((d : A)*(s : A))^n)=0 at hodd
  have hwave : wave (d*s) (n+1)=((d : A)*(s : A))^(n+1) := by
    change (((d*s)^((n+1 : ℕ) : ℤ) : unitary A) : A)=_
    rw [zpow_natCast]
    simp only [SubmonoidClass.coe_pow, Submonoid.coe_mul]
  have hdw : (d : A)*wave (d*s) (n+1)=(s : A)*((d : A)*(s : A))^n := by
    rw [hwave, pow_succ', ←mul_assoc, ←mul_assoc, hd2, one_mul]
  change τ (p*wave (d*s) (n+1)*p)=0
  rw [htr, ←mul_assoc, hp.isIdempotentElem.eq, hpform]
  rw [smul_mul_assoc, add_mul, one_mul, map_smul, map_add, hwave, hpow]
  rw [←hwave, hdw, hodd]
  simp

end Kadison.DihedralCorner

namespace Kadison

variable {A : Type*} [CStarAlgebra A] {p : A} (hp : IsStarProjection p)

lemma corner_list_prod_coe (v : List (Corner hp)) (hne : v≠[]) :
    ((v.prod : Corner hp) : A)=(v.map (fun a : Corner hp => (a : A))).prod := by
  induction v with
  | nil => exact (hne rfl).elim
  | cons a v ih =>
    by_cases hv : v=[]
    · subst v; simp
    · simp only [List.prod_cons,List.map_cons,corner_mul]
      exact congrArg ((a : A)*·) (ih hv)

lemma halfCornerTrace_tracial (τ : A →ₗ[ℂ] ℂ)
    (htr : ∀ a b : A, τ (a*b)=τ (b*a)) (a b : Corner hp) :
    halfCornerTrace hp τ (a*b)=halfCornerTrace hp τ (b*a) := by
  simp only [halfCornerTrace_apply,corner_mul,htr]

lemma halfCornerTrace_star (τ : A →ₗ[ℂ] ℂ)
    (hstar : ∀ a : A, τ (star a)=star (τ a)) (a : Corner hp) :
    halfCornerTrace hp τ (star a)=star (halfCornerTrace hp τ a) := by
  simp only [halfCornerTrace_apply,corner_star,hstar,star_mul,star_ofNat]
  exact mul_comm _ _

end Kadison

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (htr : ∀ a b : A, τ (a*b)=τ (b*a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable {p : A} (hp : IsStarProjection p) (hpd : p*(d : A)=p)

include htr hfree hij hd hs hd0 hs0 hpd in
theorem corner_cosine_pair_moment (v : List (Corner hp × ℕ)) (hne : v≠[])
    (hD : ∀ x∈v, (x.1 : A)∈S i)
    (h0 : ∀ x∈v, halfCornerTrace hp τ x.1=0) :
    halfCornerTrace hp τ ((v.map (fun x => x.1*cosine (d*s) hp (x.2+1))).prod)=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have hc : ∀ x∈v, τ (x.1 : A)=0 := by
    intro x hx
    have h := h0 x hx
    simpa only [halfCornerTrace_apply,mul_eq_zero,OfNat.ofNat_ne_zero,false_or] using h
  let letters : List (Letter S τ × ℕ) := v.attach.map (fun x =>
    (⟨i,x.1.1,hD x.1 x.2,hc x.1 x.2⟩,x.1.2))
  have hletters : letters≠[] := by simp [letters,hne]
  have hcolor : ∀ x∈letters, x.1.color≠F.color := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    exact hij
  have had : ∀ x∈letters, x.1.val*D.val=x.1.val := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx
    change (y.1.1 : A)*(d : A)=(y.1.1 : A)
    rw [←y.1.1.property.2, mul_assoc, hpd, y.1.1.property.2]
  have hm := dihedral_cyclic_moment hfree F D hij letters hletters hcolor had
  have hl : (letters.map (fun x => x.1.val*(D.val*F.val)^(x.2+1))).prod =
      (v.map (fun x => (x.1 : A)*((d : A)*(s : A))^(x.2+1))).prod := by
    exact (congrArg List.prod List.map_map).trans
      (congrArg List.prod (List.attach_map_val
        (f := fun x : Corner hp × ℕ => (x.1 : A)*((d : A)*(s : A))^(x.2+1))))
  rw [hl] at hm
  have hprod : (((v.map (fun x => x.1*cosine (d*s) hp (x.2+1))).prod : Corner hp) : A) =
      (v.map (fun x => ((x.1*cosine (d*s) hp (x.2+1) : Corner hp) : A))).prod := by
    exact (corner_list_prod_coe hp _ (by simpa using hne)).trans
      (congrArg List.prod List.map_map)
  rw [halfCornerTrace_apply,hprod]
  have hv : (v.map (fun x => ((x.1*cosine (d*s) hp (x.2+1) : Corner hp) : A))) =
      v.map (fun x => (x.1 : A)*((d : A)*(s : A))^(x.2+1)*p) := by
    apply List.map_congr_left
    intro x hx
    change (x.1 : A)*(p*wave (d*s) (x.2+1)*p)=_
    rw [←mul_assoc, ←mul_assoc, x.1.property.2]
    have he : wave (d*s) (x.2+1)=((d : A)*(s : A))^(x.2+1) := by
      change (((d*s)^((x.2+1 : ℕ) : ℤ) : unitary A) : A)=_
      rw [zpow_natCast]
      simp only [SubmonoidClass.coe_pow,Submonoid.coe_mul]
    rw [he]
  change 2*τ ((v.map (fun x => ((x.1*cosine (d*s) hp (x.2+1) : Corner hp) : A))).prod)=0
  rw [hv]
  have hr := CornerMoments.traceremove p τ htr
    (v.map (fun x => ((x.1 : A),((d : A)*(s : A))^(x.2+1))))
    (by simpa using hne) (by
      intro x hx; obtain ⟨y,_,rfl⟩ := List.mem_map.mp hx; exact y.1.property.1)
  simp only [List.map_map,Function.comp_def] at hr
  rw [hr,hm,mul_zero]

end Kadison.DihedralCorner

namespace Kadison.FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable {S : Bool → StarSubalgebra ℂ A} {τ : A →ₗ[ℂ] ℂ}

lemma word_flattenPairs (v : List (Letter S τ × Letter S τ)) :
    word (flattenPairs v)=(v.map (fun x => x.1.val*x.2.val)).prod := by
  induction v with
  | nil => rfl
  | cons x v ih => simp only [flattenPairs_cons, word_cons, ih, List.map_cons,
      List.prod_cons, mul_assoc]

lemma flattenPairs_parse (a b : Letter S τ) (m : List (Letter S τ))
    (ha : a.color=false) (hb : b.color=true) (hw : Reduced (a::m++[b])) :
    ∃ v : List (Letter S τ × Letter S τ), v≠[] ∧
      flattenPairs v=a::m++[b] ∧ ∀ x∈v, x.1.color=false ∧ x.2.color=true := by
  induction hn : m.length using Nat.strong_induction_on generalizing a m with
  | h n ih =>
    cases m with
    | nil => exact ⟨[(a,b)],by simp,by rfl,by intro x hx; obtain rfl := List.mem_singleton.mp hx; exact ⟨ha,hb⟩⟩
    | cons c m =>
      have hc : c.color=true := by
        have hac : a.color≠c.color := hw.rel
        cases hcc : c.color <;> simp_all
      cases m with
      | nil =>
        have hcb : c.color≠b.color := hw.tail.rel
        exact (hcb (hc.trans hb.symm)).elim
      | cons d m =>
        have hd : d.color=false := by
          have hcd : c.color≠d.color := hw.tail.rel
          cases hdd : d.color <;> simp_all
        obtain ⟨v,hv,hvw,hvc⟩ := ih m.length (by simp at hn; omega) d m hd hw.tail.tail rfl
        refine ⟨(a,c)::v,by simp,?_,?_⟩
        · simp only [flattenPairs_cons, hvw, List.cons_append]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl|hx
          · exact ⟨ha,hc⟩
          · exact hvc x hx

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a))

include h1 htr hstar in
theorem free_bool_of_pair_moments
    (hpair : ∀ v : List (Letter S τ × Letter S τ), v≠[] →
      (∀ x∈v, x.1.color=false ∧ x.2.color=true) →
      τ ((v.map (fun x => x.1.val*x.2.val)).prod)=0) : Free S τ := by
  apply free_of_different_endpoints S τ h1 htr
  intro a b m hw hab
  have hdir : ∀ (a b : Letter S τ) (m : List (Letter S τ)),
      a.color=false → b.color=true → Reduced (a::m++[b]) → τ (word (a::m++[b]))=0 := by
    intro a b m ha hb hw
    obtain ⟨v,hv,hvw,hvc⟩ := flattenPairs_parse a b m ha hb hw
    rw [←hvw,word_flattenPairs]
    exact hpair v hv hvc
  cases ha : a.color with
  | false =>
    have hb : b.color=true := by cases hb : b.color <;> simp_all
    exact hdir a b m ha hb hw
  | true =>
    have hb : b.color=false := by cases hb : b.color <;> simp_all
    have heq : reverseStar hstar (a::m++[b]) =
        b.conj hstar :: reverseStar hstar m ++ [a.conj hstar] := by
      simp [reverseStar]
    have hz := hdir (b.conj hstar) (a.conj hstar) (reverseStar hstar m) hb ha
      (by rw [←heq]; exact hw.reverseStar hstar)
    rw [←heq,word_reverseStar,hstar] at hz
    exact star_eq_zero.mp hz

omit [StarRing A] [StarModule ℂ A] in
lemma paired_vanish_on_spans (B : Set A) (a : List A) (φ : A →ₗ[ℂ] ℂ)
    (h : ∀ b : List A, List.Forall₂ (fun _ x => x∈B) a b →
      φ ((List.zipWith (·*·) a b).prod)=0) :
    ∀ b : List A, List.Forall₂ (fun _ x => x∈Submodule.span ℂ B) a b →
      φ ((List.zipWith (·*·) a b).prod)=0 := by
  induction a generalizing φ with
  | nil => intro b hb; cases hb; exact h [] .nil
  | cons a as ih =>
    intro b hb
    cases hb with
    | cons hx hbs =>
      rename_i x xs
      let ψ : A →ₗ[ℂ] ℂ := φ.comp (LinearMap.mulLeft ℂ (a*x))
      apply ih ψ ?_ xs hbs
      intro ys hys
      change φ ((a*x)*(List.zipWith (·*·) as ys).prod)=0
      induction hx using Submodule.span_induction with
      | mem x hx => exact h (x::ys) (.cons hx hys)
      | zero => simp
      | add x y _ _ hx hy => simp only [mul_add, add_mul, map_add, hx,hy,add_zero]
      | smul c x _ hx => simp only [mul_smul_comm,smul_mul_assoc,map_smul,hx,smul_zero]

end Kadison.FreeMoments

namespace Kadison.FreeMoments

lemma pair_generators_witness {A I : Type*} (c : I → A) {a b : List A}
    (hb : List.Forall₂ (fun _ x => x∈Set.range c) a b) :
    ∃ v : List (A×I), v.map Prod.fst=a ∧ v.map (fun x => c x.2)=b := by
  induction hb with
  | nil => exact ⟨[],rfl,rfl⟩
  | @cons a b as bs hb hbs ih =>
    obtain ⟨i,rfl⟩ := hb
    obtain ⟨v,rfl,rfl⟩ := ih
    exact ⟨(a,i)::v,rfl,rfl⟩

lemma zipWith_same_maps {A B C E : Type*} (m : B → C → E) (f : A → B) (g : A → C)
    (v : List A) : List.zipWith m (v.map f) (v.map g) = v.map (fun x => m (f x) (g x)) := by
  induction v with
  | nil => rfl
  | cons a v ih => simp only [List.map_cons,List.zipWith_cons_cons,ih]

variable {A : Type*} [Ring A] [Algebra ℂ A]

lemma pairs_vanish_on_second_span {I : Type*} (F : Set A) (c : I → A)
    (φ : A →ₗ[ℂ] ℂ)
    (h : ∀ v : List (A×I), v≠[] → (∀ x∈v,x.1∈F) →
      φ ((v.map (fun x => x.1*c x.2)).prod)=0)
    (v : List (A×A)) (hne : v≠[])
    (hF : ∀ x∈v,x.1∈F) (hB : ∀ x∈v,x.2∈Submodule.span ℂ (Set.range c)) :
    φ ((v.map (fun x => x.1*x.2)).prod)=0 := by
  have hz := paired_vanish_on_spans (Set.range c) (v.map Prod.fst) φ (fun b hb => ?_)
    (v.map Prod.snd) (by
      rw [List.forall₂_map_left_iff,List.forall₂_map_right_iff,List.forall₂_same]
      exact hB)
  · simpa only [zipWith_same_maps] using hz
  obtain ⟨w,hw,hwb⟩ := pair_generators_witness c hb
  have hwne : w≠[] := by
    intro he; simp only [he,List.map_nil] at hw
    exact hne (List.map_eq_nil_iff.mp hw.symm)
  have hwF : ∀ x∈w,x.1∈F := by
    intro x hx
    have hm : x.1∈v.map Prod.fst := hw ▸ List.mem_map_of_mem hx
    obtain ⟨y,hy,hxy⟩ := List.mem_map.mp hm
    exact hxy ▸ hF y hy
  rw [←hw,←hwb,zipWith_same_maps]
  exact h w hwne hwF

end Kadison.FreeMoments

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d : A)*(d : A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include h1 hd0 hpform in
lemma halfCornerTrace_one : halfCornerTrace hp τ 1=1 := by
  simp only [halfCornerTrace_apply,corner_one,hpform,map_smul,map_add,h1,hd0]
  norm_num

include htr hfree hij hd hs hd0 hs0 hr hd2 hpform hpd hdp in
lemma cosine_centered (n : ℤ) (hn : n≠0) : halfCornerTrace hp τ (cosine (d*s) hp n)=0 := by
  have hpos (m : ℕ) : halfCornerTrace hp τ (cosine (d*s) hp (m+1))=0 := by
    rw [halfCornerTrace_apply,
      cosine_positive_centered τ htr hfree d s i j hij hd hs hd0 hs0 hp hpform hd2,mul_zero]
  cases n with
  | ofNat n =>
    cases n with
    | zero => exact (hn rfl).elim
    | succ m => exact hpos m
  | negSucc m =>
    change halfCornerTrace hp τ (cosine (d*s) hp (-((m+1 : ℕ) : ℤ)))=0
    rw [cosine_neg (d*s) d hr hp hpd hdp]
    exact hpos m

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
theorem corner_cosine_free (hpD : p∈S i) :
    Free (cornerPairFactors (S:=S) d s i hr hp hpform hdp hpD) (halfCornerTrace hp τ) := by
  let R := cornerPairFactors (S:=S) d s i hr hp hpform hdp hpD
  have hτ1 := halfCornerTrace_one τ h1 d hd0 hp hpform
  have hτ0 := cosine_centered τ htr hfree d s i j hij hd hs hd0 hs0 hr hd2 hp hpform hpd hdp
  apply free_bool_of_pair_moments (S := R) (τ := halfCornerTrace hp τ) hτ1
    (halfCornerTrace_tracial hp τ htr) (halfCornerTrace_star hp τ hstar)
  intro v hv hcolor
  let F : Set (Corner hp) := {a | (a : A)∈S i ∧ halfCornerTrace hp τ a=0}
  have hD : ∀ x∈v, x.1.val∈F := by
    intro x hx
    have hm := x.1.mem
    rw [(hcolor x hx).1] at hm
    exact ⟨hm,x.1.centered⟩
  have hB : ∀ x∈v, x.2.val∈Submodule.span ℂ (positiveCosines (d*s) hp) := by
    intro x hx
    have hm := x.2.mem
    rw [(hcolor x hx).2] at hm
    exact centered_cosineAlgebra_span (d*s) d hr hp hpform hpd hdp
      (halfCornerTrace hp τ) hτ1 hτ0 hm x.2.centered
  have hz := pairs_vanish_on_second_span F (fun n : ℕ => cosine (d*s) hp (n+1))
    (halfCornerTrace hp τ)
    (fun w hw hwF => corner_cosine_pair_moment τ htr hfree d s i j hij hd hs hd0 hs0 hp hpd
      w hw (fun x hx => (hwF x hx).1) (fun x hx => (hwF x hx).2))
    (v.map (fun x => (x.1.val,x.2.val))) (by simpa using hv) (by
      intro x hx; obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx; exact hD y hy) (by
      intro x hx; obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx; exact hB y hy)
  simpa only [List.map_map,Function.comp_def] using hz

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DihedralHaar
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.DihedralCorner

open FreeMoments

variable {A : Type*} [CStarAlgebra A]

variable {ι : Type*} {S : ι → StarSubalgebra ℂ A} (τ : A →ₗ[ℂ] ℂ)

variable (h1 : τ 1=1) (htr : ∀ a b : A, τ (a*b)=τ (b*a))
  (hstar : ∀ a : A, τ (star a)=star (τ a)) (hfree : Free S τ)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d : A)∈S i) (hs : (s : A)∈S j)
  (hd0 : τ (d : A)=0) (hs0 : τ (s : A)=0)

lemma wave_nat (u : unitary A) (n : ℕ) : wave u (n:ℤ)=(u:A)^n := by
  simp only [wave,zpow_natCast,SubmonoidClass.coe_pow]

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FejerTest
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators InnerProductSpace ComplexOrder

namespace Kadison.FejerTest

variable {A : Type*} [CStarAlgebra A]

lemma norm_powerAverage_le (w : A) (m : ℕ) (hm : 0 < m) (hw : ‖w‖ ≤ 1) :
    ‖powerAverage w m‖ ≤ 1 := by
  nontriviality A
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  unfold powerAverage
  rw [norm_smul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (m : ℝ)⁻¹ * ∑ _i ∈ Finset.range m, (1 : ℝ) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (le_of_lt hm'))
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      cases i with
      | zero => simp
      | succ i =>
        exact (norm_pow_le' w (Nat.succ_pos i)).trans
          ((pow_le_pow_left₀ (norm_nonneg _) hw _).trans_eq (one_pow _))
    _ = 1 := by simp [ne_of_gt hm']

lemma testPolynomial_selfAdjoint (w : A) (m : ℕ) :
    IsSelfAdjoint (testPolynomial w m) := by
  unfold testPolynomial
  exact (IsSelfAdjoint.star_mul_self _).sub
    (IsSelfAdjoint.smul (by simp [IsSelfAdjoint]) (IsSelfAdjoint.one A))

lemma norm_testPolynomial_le (w : A) (m : ℕ) (hm : 0 < m) (hw : ‖w‖ ≤ 1) :
    ‖testPolynomial w m‖ ≤ 2 := by
  nontriviality A
  have hq := norm_powerAverage_le w m hm hw
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  calc
    _ ≤ ‖star (powerAverage w m) * powerAverage w m‖ + ‖((m : ℂ)⁻¹) • (1 : A)‖ :=
      norm_sub_le _ _
    _ ≤ 1+1 := by
      apply add_le_add
      · apply (norm_mul_le _ _).trans
        simpa only [norm_star, mul_one] using
          (mul_le_mul hq hq (norm_nonneg _) zero_le_one)
      · rw [norm_smul, norm_inv, Complex.norm_natCast]
        exact (mul_le_mul_of_nonneg_left (le_of_eq (norm_one (α := A))) (by positivity)).trans
          (by simpa using (inv_le_one₀ (by positivity : (0 : ℝ) < m)).mpr hm')
    _ = 2 := by norm_num

end Kadison.FejerTest

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_DihedralFejer
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped BigOperators ComplexOrder

namespace Kadison.DihedralCorner

open FreeMoments FejerTest

variable {A : Type*} [CStarAlgebra A]

lemma star_pow_mul_pow (u : unitary A) (i j : ℕ) :
    star ((u:A)^i)*(u:A)^j=wave u (-(i:ℤ)+(j:ℤ)) := by
  rw [←wave_nat,←wave_nat,wave_star,←wave_add]

lemma testPolynomial_expansion (u : unitary A) (m : ℕ) :
    testPolynomial (u:A) m=
      ((m:ℂ)⁻¹*(m:ℂ)⁻¹) •
        (∑ i∈Finset.range m,∑ j∈Finset.range m,wave u (-(i:ℤ)+(j:ℤ))) -
      (m:ℂ)⁻¹ • (1:A) := by
  have hs : star ((m:ℂ)⁻¹)=(m:ℂ)⁻¹ := by simp
  simp only [testPolynomial,powerAverage,star_smul,
    star_sum,smul_mul_assoc,mul_smul_comm,Finset.sum_mul,Finset.mul_sum,
    star_pow_mul_pow,hs,←Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]

variable {p : A} (hp : IsStarProjection p)

lemma fejerCorner_mem (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)
    (hpform : p=(1/2:ℂ) • (1+(d:A))) (hdp : (d:A)*p=p) (m : ℕ) :
    fejerCorner hp u m∈cosineAlgebra u d hr hp hpform hdp := by
  let R := cosineAlgebra u d hr hp hpform hdp
  unfold fejerCorner
  rw [testPolynomial_expansion]
  simp only [map_sub,map_smul,map_sum,compressCorner_wave,compressCorner_one]
  exact R.sub_mem (R.smul_mem (R.sum_mem (fun i _ =>
    R.sum_mem (fun j _ => cosine_mem u hp _))) _) (R.smul_mem R.one_mem _)

lemma fejerCorner_selfAdjoint (u : unitary A) (m : ℕ) :
    IsSelfAdjoint (fejerCorner hp u m) := by
  change star (fejerCorner hp u m)=fejerCorner hp u m
  apply Subtype.ext
  change star (p*testPolynomial (u:A) m*p)=p*testPolynomial (u:A) m*p
  simp only [star_mul,hp.isSelfAdjoint.star_eq,(testPolynomial_selfAdjoint (u:A) m).star_eq]
  exact (mul_assoc _ _ _).symm

lemma fejerCorner_norm_le (u : unitary A) (m : ℕ) (hm : 0 < m) :
    ‖fejerCorner hp u m‖≤2 := by
  nontriviality A
  change ‖p*testPolynomial (u:A) m*p‖≤2
  have hp1 : ‖p‖≤1 := hp.norm_le
  have hq := norm_testPolynomial_le (u:A) m hm (le_of_eq (CStarRing.norm_coe_unitary u))
  calc
    _ ≤ ‖p‖*‖testPolynomial (u:A) m‖*‖p‖ := norm_mul₃_le
    _ ≤ 1*2*1 := mul_le_mul
      (mul_le_mul hp1 hq (norm_nonneg _) zero_le_one) hp1 (norm_nonneg _) (by norm_num)
    _ = 2 := by norm_num

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCreation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ComplexOrder InnerProductSpace
open Complex ContinuousLinearMap UniformSpace Completion
open scoped InnerProductSpace
open scoped TensorProduct
open scoped TensorProduct InnerProductSpace Topology
open UniformSpace Completion Filter
open scoped TensorProduct
open UniformSpace Completion
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
open scoped InnerProductSpace TensorProduct ComplexOrder
open UniformSpace
open scoped InnerProductSpace _root_.Topology

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

include hfree in
lemma inner_mul_wordVector {i : ι} {w z : List (Letter t S)}
    (hw : Reduced w) (hz : Reduced z)
    (hiw : CanPrepend t S i w) (hiz : CanPrepend t S i z)
    {a : A} (ha : a ∈ S i) :
    inner ℂ (t.functional.gnsStarAlgHom a (wordVector t S w))
      (t.functional.gnsStarAlgHom a (wordVector t S z)) =
      t.functional (star a * a) * inner ℂ (wordVector t S w) (wordVector t S z) := by
  rw [mul_wordVector, mul_wordVector, Completion.inner_coe, inner_wordVector]
  change t.functional (star (a * word w) * (a * word z)) = _
  simpa only [star_mul, mul_assoc] using
    middle_factor t S hfree hw hz hiw hiz (mul_mem (star_mem ha) ha)

include hfree in
lemma inner_mul_tailSpan (i : ι) {a : A} (ha : a ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpan t S i) (hy : y ∈ tailSpan t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, hw, hiw, rfl⟩ := hx
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, hiz, rfl⟩ := hy
      exact inner_mul_wordVector t S hfree hw hz hiw hiz ha
    | zero => simp
    | add y z _ _ hy hz => simp only [map_add, inner_add_right, hy, hz, mul_add]
    | smul c y _ hy => simp only [map_smul, inner_smul_right, hy]; ring
  | zero => simp
  | add x z _ _ hx hz => simp only [map_add, inner_add_left, hx, hz, mul_add]
  | smul c x _ hx => simp only [map_smul, inner_smul_left, hx]; ring

include hfree in
lemma inner_mul_tailSpace (i : ι) {a : A} (ha : a ∈ S i)
    {x y : t.functional.GNS} (hx : x ∈ tailSpace t S i) (hy : y ∈ tailSpace t S i) :
    inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y := by
  apply closure_minimal (s := (tailSpan t S i : Set _))
    (t := {x | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
      t.functional (star a * a) * inner ℂ x y}) ?_ ?_ hx
  · intro x hx
    apply closure_minimal (s := (tailSpan t S i : Set _))
      (t := {y | inner ℂ (t.functional.gnsStarAlgHom a x) (t.functional.gnsStarAlgHom a y) =
        t.functional (star a * a) * inner ℂ x y}) ?_ ?_ hy
    · intro y hy
      exact inner_mul_tailSpan t S hfree i ha hx hy
    · apply isClosed_eq <;> fun_prop
  · apply isClosed_eq <;> fun_prop

include hfree in
lemma norm_mul_tailSpace (i : ι) {a : A} (ha : a ∈ S i)
    {x : t.functional.GNS} (hx : x ∈ tailSpace t S i) :
    ‖t.functional.gnsStarAlgHom a x‖ = ‖t.functional.toPreGNS a‖ * ‖x‖ := by
  have h := inner_mul_tailSpace t S hfree i ha hx hx
  have hn := t.functional.preGNS_norm_sq (t.functional.toPreGNS a)
  change (‖t.functional.toPreGNS a‖ : ℂ) ^ 2 = t.functional (star a * a) at hn
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, ← hn] at h
  have hr : ‖t.functional.gnsStarAlgHom a x‖ ^ 2 =
      ‖t.functional.toPreGNS a‖ ^ 2 * ‖x‖ ^ 2 := by
    have hr := congrArg Complex.re h
    simpa only [RCLike.ofReal_eq_complex_ofReal, ← Complex.ofReal_pow,
      ← Complex.ofReal_mul, Complex.ofReal_re] using hr
  nlinarith [norm_nonneg (t.functional.gnsStarAlgHom a x),
    mul_nonneg (norm_nonneg (t.functional.toPreGNS a)) (norm_nonneg x)]

include hfree in
lemma headSpace_le_tailSpace_orthogonal (i : ι) :
    headSpace t S i ≤ (tailSpace t S i)ᗮ := by
  apply (headSpan t S i).topologicalClosure_minimal ?_ (Submodule.isClosed_orthogonal _)
  rw [tailSpace, Submodule.orthogonal_closure]
  apply Submodule.span_le.mpr
  rintro x ⟨z, hz, ⟨a, z, rfl, ha⟩, rfl⟩
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, hiw, rfl⟩ := hy
    rw [inner_wordVector]
    change t.functional.toLinearMap (star (word w) * word (a :: z)) = 0
    rw [gram_word (fun a => map_star t.functional a) t.normalized hfree _ _ hw hz]
    exact gram_zero_of_colors_ne _ _ (colors_ne_prepend t S hiw a ha)
  | zero => simp
  | add y z _ _ hy hz => simp [inner_add_left, hy, hz]
  | smul c y _ hy => simp [inner_smul_left, hy]

lemma wordVector_mem_head_sup_tail (i : ι) (w : List (Letter t S)) (hw : Reduced w) :
    wordVector t S w ∈ headSpace t S i ⊔ tailSpace t S i := by
  classical
  cases w with
  | nil =>
    apply Submodule.mem_sup_right
    apply (tailSpan t S i).le_topologicalClosure
    exact Submodule.subset_span ⟨[], hw, by simp [CanPrepend], rfl⟩
  | cons a w =>
    by_cases hi : a.color = i
    · apply Submodule.mem_sup_left
      apply (headSpan t S i).le_topologicalClosure
      exact Submodule.subset_span ⟨a :: w, hw, ⟨a, w, rfl, hi⟩, rfl⟩
    · apply Submodule.mem_sup_right
      apply (tailSpan t S i).le_topologicalClosure
      exact Submodule.subset_span ⟨a :: w, hw, by simpa [CanPrepend] using Ne.symm hi, rfl⟩

lemma generated_mem_head_sup_tail (i : ι) {a : A} (ha : a ∈ iSup S) :
    (t.functional.toPreGNS a : t.functional.GNS) ∈ headSpace t S i ⊔ tailSpace t S i := by
  have ha' : a ∈ FreeMoments.wordSpan S t.functional.toLinearMap := by
    change a ∈ (FreeMoments.reducedAlgebra S (fun a => map_star t.functional a) t.normalized)
    rw [FreeMoments.reducedAlgebra_eq_iSup]
    exact ha
  clear ha
  induction ha' using Submodule.span_induction with
  | mem a ha =>
    obtain ⟨w, hw, rfl⟩ := ha
    exact wordVector_mem_head_sup_tail t S i w hw
  | zero => simp only [map_zero, Completion.coe_zero, Submodule.zero_mem]
  | add a b _ _ ha hb => simpa only [map_add, Completion.coe_add] using
      (headSpace t S i ⊔ tailSpace t S i).add_mem ha hb
  | smul c a _ ha => simpa only [map_smul, Completion.coe_smul] using
      (headSpace t S i ⊔ tailSpace t S i).smul_mem c ha

lemma total_head_sup_tail (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    (headSpace t S i ⊔ tailSpace t S i).topologicalClosure = ⊤ := by
  apply Submodule.eq_top_iff'.mpr
  intro x
  induction x using Completion.induction_on with
  | hp => exact (headSpace t S i ⊔ tailSpace t S i).isClosed_topologicalClosure
  | ih x =>
    let ξ : t.functional.GNS := (t.functional.toPreGNS 1 : t.functional.GNS)
    have h := Kadison.bicommutant_mem_cyclicSubspace (generatedOperators t S)
      (hgen (t.functional.ofPreGNS x)) ξ
    have heq : t.functional.gnsStarAlgHom (t.functional.ofPreGNS x) ξ =
        (x : t.functional.GNS) := by
      simp [ξ, PositiveLinearMap.gnsStarAlgHom]
    rw [heq] at h
    apply Submodule.topologicalClosure_mono ?_ h
    rintro y ⟨a, ha, rfl⟩
    obtain ⟨b, hb, rfl⟩ := ha
    simpa [ξ, PositiveLinearMap.gnsStarAlgHom] using generated_mem_head_sup_tail t S i hb

include hfree in
lemma headSpace_eq_tailSpace_orthogonal (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    headSpace t S i = (tailSpace t S i)ᗮ := by
  apply le_antisymm (headSpace_le_tailSpace_orthogonal t S hfree i)
  intro x hx
  let P := headSpace t S i
  have hp : P.starProjection x ∈ P := P.starProjection_apply_mem x
  have hy : x - P.starProjection x ∈ Pᗮ ⊓ (tailSpace t S i)ᗮ :=
    ⟨P.sub_starProjection_mem_orthogonal x,
      (tailSpace t S i)ᗮ.sub_mem hx (headSpace_le_tailSpace_orthogonal t S hfree i hp)⟩
  have hbot : Pᗮ ⊓ (tailSpace t S i)ᗮ = ⊥ := by
    rw [Submodule.inf_orthogonal, ← Submodule.orthogonal_closure,
      total_head_sup_tail t S i hgen, Submodule.top_orthogonal_eq_bot]
  rw [hbot, Submodule.mem_bot] at hy
  rw [sub_eq_zero.mp hy]
  exact hp

end Kadison.FreeCreation
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeCompressionNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeCorner

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma three_block_bound (E P T : H →L[ℂ] H) {a b : ℝ}
    (hE : ‖E‖ ≤ 1)
    (hzero : (1-P)*T*(1-P) = 0)
    (hleft : ‖E*P‖ ≤ a) (hright : ‖P*E‖ ≤ a)
    (hcreate : ‖T*(1-P)‖ ≤ b) (hannihilate : ‖(1-P)*T‖ ≤ b) :
    ‖E*T*E‖ ≤ 2*a*b + a*a*‖T‖ := by
  have ha : 0 ≤ a := (norm_nonneg _).trans hleft
  have hb : 0 ≤ b := (norm_nonneg _).trans hcreate
  have hid : E*T*E = (E*P)*(T*(1-P))*E +
      E*((1-P)*T)*(P*E) + (E*P)*T*(P*E) := by
    calc
      E*T*E = (E*P)*(T*(1-P))*E + E*((1-P)*T)*(P*E) +
        (E*P)*T*(P*E) + E*((1-P)*T*(1-P))*E := by noncomm_ring
      _ = _ := by rw [hzero, mul_zero, zero_mul, add_zero]
  have h1 : ‖(E*P)*(T*(1-P))*E‖ ≤ a*b := by
    calc
      _ ≤ ‖E*P‖ * ‖T*(1-P)‖ * ‖E‖ := norm_mul₃_le
      _ ≤ a*b*1 := mul_le_mul
        (mul_le_mul hleft hcreate (norm_nonneg _) ha) hE (norm_nonneg _) (mul_nonneg ha hb)
      _ = _ := mul_one _
  have h2 : ‖E*((1-P)*T)*(P*E)‖ ≤ a*b := by
    calc
      _ ≤ ‖E‖ * ‖(1-P)*T‖ * ‖P*E‖ := norm_mul₃_le
      _ ≤ 1*b*a := mul_le_mul
        (mul_le_mul hE hannihilate (norm_nonneg _) zero_le_one) hright
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have h3 : ‖(E*P)*T*(P*E)‖ ≤ a*a*‖T‖ := by
    calc
      _ ≤ ‖E*P‖ * ‖T‖ * ‖P*E‖ := norm_mul₃_le
      _ ≤ a*‖T‖*a := mul_le_mul
        (mul_le_mul_of_nonneg_right hleft (norm_nonneg _)) hright
        (norm_nonneg _) (by positivity)
      _ = _ := by ring
  rw [hid]
  exact (norm_add₃_le).trans (by linarith)

end Kadison.FreeCorner

namespace Kadison.FreeCreation

open FreeMoments FreeWordTensor

open scoped InnerProductSpace

open UniformSpace

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S t.functional.toLinearMap)

lemma gns_injective : Function.Injective t.functional.gnsStarAlgHom := by
  intro a b hab
  have h := congrArg (fun T : t.functional.GNS →L[ℂ] t.functional.GNS =>
    T (t.functional.toPreGNS 1 : t.functional.GNS)) hab
  have hab' : (t.functional.toPreGNS a : t.functional.GNS) =
      (t.functional.toPreGNS b : t.functional.GNS) := by
    simpa [PositiveLinearMap.gnsStarAlgHom] using h
  exact t.functional.toPreGNS.injective (Completion.coe_injective _ hab')

lemma norm_gns (a : A) : ‖t.functional.gnsStarAlgHom a‖ = ‖a‖ :=
  NonUnitalStarAlgHom.norm_map _ (gns_injective t) a

lemma norm_preGNS_projection {e : A} (he : IsStarProjection e) :
    ‖t.functional.toPreGNS e‖ = Real.sqrt (t.functional e).re := by
  rw [t.functional.preGNS_norm_def]
  simp only [PositiveLinearMap.ofPreGNS_toPreGNS, he.isSelfAdjoint.star_eq,
    he.isIdempotentElem.eq]

lemma norm_preGNS_projection_sq {e : A} (he : IsStarProjection e) :
    ‖t.functional.toPreGNS e‖ ^ 2 = (t.functional e).re := by
  have hn := t.functional.preGNS_norm_sq (t.functional.toPreGNS e)
  have h := congrArg Complex.re hn
  simpa only [PositiveLinearMap.ofPreGNS_toPreGNS, he.isSelfAdjoint.star_eq,
    he.isIdempotentElem.eq, RCLike.ofReal_eq_complex_ofReal,
    ← Complex.ofReal_pow, Complex.ofReal_re] using h

include hfree in
lemma one_sub_headProjection (i : ι)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    1 - (headSpace t S i).starProjection = (tailSpace t S i).starProjection := by
  simp only [headSpace_eq_tailSpace_orthogonal t S hfree i hgen,
    Submodule.starProjection_orthogonal', sub_sub_cancel]

include hfree in
lemma norm_left_headProjection {i j : ι} (hij : i ≠ j) {a : A} (ha : a ∈ S i) :
    ‖t.functional.gnsStarAlgHom a * (headSpace t S j).starProjection‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖t.functional.gnsStarAlgHom a ((headSpace t S j).starProjection x)‖ ≤ _
  rw [norm_mul_tailSpace t S hfree i ha
    (headSpace_le_other_tailSpace t S hij.symm ((headSpace t S j).starProjection_apply_mem x))]
  exact mul_le_mul_of_nonneg_left ((headSpace t S j).norm_starProjection_apply_le x)
    (norm_nonneg _)

include hfree in
lemma norm_right_headProjection {i j : ι} (hij : i ≠ j) {a : A}
    (ha : a ∈ S i) (haStar : IsSelfAdjoint a) :
    ‖(headSpace t S j).starProjection * t.functional.gnsStarAlgHom a‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  have heq : star (t.functional.gnsStarAlgHom a * (headSpace t S j).starProjection) =
      (headSpace t S j).starProjection * t.functional.gnsStarAlgHom a := by
    rw [star_mul, (isSelfAdjoint_starProjection _).star_eq,
      (haStar.map t.functional.gnsStarAlgHom).star_eq]
  rw [← heq, norm_star]
  exact norm_left_headProjection t S hfree hij ha

include hfree in
lemma norm_creation (i : ι) {a : A} (ha : a ∈ S i) :
    ‖t.functional.gnsStarAlgHom a * (tailSpace t S i).starProjection‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  change ‖t.functional.gnsStarAlgHom a ((tailSpace t S i).starProjection x)‖ ≤ _
  rw [norm_mul_tailSpace t S hfree i ha ((tailSpace t S i).starProjection_apply_mem x)]
  exact mul_le_mul_of_nonneg_left ((tailSpace t S i).norm_starProjection_apply_le x)
    (norm_nonneg _)

include hfree in
lemma norm_annihilation (i : ι) {a : A} (ha : a ∈ S i) (haStar : IsSelfAdjoint a) :
    ‖(tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a‖ ≤
      ‖t.functional.toPreGNS a‖ := by
  have heq : star (t.functional.gnsStarAlgHom a * (tailSpace t S i).starProjection) =
      (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a := by
    rw [star_mul, (isSelfAdjoint_starProjection _).star_eq,
      (haStar.map t.functional.gnsStarAlgHom).star_eq]
  rw [← heq, norm_star]
  exact norm_creation t S hfree i ha

include hfree in
lemma creation_zero_block (i : ι) {a : A} (ha : a ∈ S i) (ha0 : t.functional a = 0) :
    (tailSpace t S i).starProjection * t.functional.gnsStarAlgHom a *
      (tailSpace t S i).starProjection = 0 := by
  ext x
  change (tailSpace t S i).starProjection
    (t.functional.gnsStarAlgHom a ((tailSpace t S i).starProjection x)) = 0
  rw [Submodule.starProjection_apply, Submodule.coe_eq_zero]
  apply Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal
  apply headSpace_le_tailSpace_orthogonal t S hfree i
  exact creation_mem_headSpace t S i ha ha0 ((tailSpace t S i).starProjection_apply_mem x)

include hfree in
theorem free_compression_norm {i j : ι} (hij : i ≠ j) {e b : A}
    (he : IsStarProjection e) (he_mem : e ∈ S i)
    (hb : IsSelfAdjoint b) (hb_mem : b ∈ S j) (hb0 : t.functional b = 0)
    (hgen : ∀ a : A, t.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators t S : Set _))) :
    ‖e*b*e‖ ≤ 2 * Real.sqrt (t.functional e).re * ‖t.functional.toPreGNS b‖ +
      (t.functional e).re * ‖b‖ := by
  let π := t.functional.gnsStarAlgHom
  let P := (headSpace t S j).starProjection
  have hP : 1 - P = (tailSpace t S j).starProjection :=
    one_sub_headProjection t S hfree j hgen
  have h := Kadison.FreeCorner.three_block_bound (π e) P (π b)
    (a := ‖t.functional.toPreGNS e‖) (b := ‖t.functional.toPreGNS b‖)
    ((he.map π).norm_le _) (by rw [hP]; exact creation_zero_block t S hfree j hb_mem hb0)
    (norm_left_headProjection t S hfree hij he_mem)
    (norm_right_headProjection t S hfree hij he_mem he.isSelfAdjoint)
    (by rw [hP]; exact norm_creation t S hfree j hb_mem)
    (by rw [hP]; exact norm_annihilation t S hfree j hb_mem hb)
  have hn : ‖t.functional.toPreGNS e‖ * ‖t.functional.toPreGNS e‖ =
      (t.functional e).re := by simpa only [pow_two] using norm_preGNS_projection_sq t he
  rw [hn, norm_preGNS_projection t he] at h
  simpa only [π, ← map_mul, norm_gns] using h

end Kadison.FreeCreation

namespace Kadison.FreeMoments

variable {A B : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]
  [Ring B] [Algebra ℂ B] [StarRing B] [StarModule ℂ B]

variable {ι : Type*} (S : ι → StarSubalgebra ℂ A) (τ : A →ₗ[ℂ] ℂ)
  (f : B →⋆ₐ[ℂ] A)

lemma word_liftLetter (w : List (Letter (fun i => (S i).comap f) (τ.comp f.toLinearMap))) :
    word (w.map (liftLetter S τ f))=f (word w) := by
  induction w with
  | nil => simp
  | cons a w ih => simp only [List.map_cons,word_cons,liftLetter_val,ih,map_mul]

lemma Free.comap (h : Free S τ) : Free (fun i => (S i).comap f) (τ.comp f.toLinearMap) := by
  intro w hw hne
  have hr : Reduced (w.map (liftLetter S τ f)) := by
    rw [Reduced,List.isChain_map]
    exact hw
  have hz := h (w.map (liftLetter S τ f)) hr (by simpa using hne)
  change τ (f (word w))=0
  rwa [word_liftLetter] at hz

end Kadison.FreeMoments

namespace Kadison.FreeCreation

open FreeWordTensor

open scoped ComplexOrder

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : FreeMoments.Free S t.functional.toLinearMap)

include hfree in
theorem free_compression_norm_intrinsic {i j : ι} (hij : i≠j) {e b : A}
    (he : IsStarProjection e) (he_mem : e∈S i)
    (hb : IsSelfAdjoint b) (hb_mem : b∈S j) (hb0 : t.functional b=0) :
    ‖e*b*e‖ ≤ 2*Real.sqrt (t.functional e).re*‖t.functional.toPreGNS b‖ +
      (t.functional e).re*‖b‖ := by
  let C := (iSup S).topologicalClosure
  let : IsClosed (C : Set A) := StarSubalgebra.isClosed_topologicalClosure _
  let : PartialOrder C := CStarAlgebra.spectralOrder C
  let : StarOrderedRing C := CStarAlgebra.spectralOrderedRing C
  let f : C →⋆ₐ[ℂ] A := C.subtype
  let tC := restrictedState t f Subtype.val_injective
  let R : ι → StarSubalgebra ℂ C := fun i => (S i).comap f
  have hR : FreeMoments.Free R tC.functional.toLinearMap := hfree.comap S _ f
  have hinc : iSup S ≤ (iSup R).map f := by
    apply iSup_le
    intro k a ha
    exact ⟨⟨a,StarSubalgebra.le_topologicalClosure _ ((le_iSup S k) ha)⟩,
      (le_iSup R k) ha,rfl⟩
  have hgen : ∀ a : C, tC.functional.gnsStarAlgHom a ∈
      Set.centralizer (Set.centralizer (generatedOperators tC R : Set _)) := by
    let inc : ↥(iSup S) → C := fun x => ⟨x.val,StarSubalgebra.le_topologicalClosure _ x.property⟩
    have hd : DenseRange inc := by
      change DenseRange (Set.inclusion (StarSubalgebra.le_topologicalClosure (iSup S)))
      apply (denseRange_inclusion_iff _).2
      exact fun _ h => h
    intro a
    apply closure_minimal (s := Set.range inc) ?_
      ((Set.isClosed_centralizer _).preimage
        (AddMonoidHomClass.continuous_of_bound tC.functional.gnsStarAlgHom 1
          (by intro x; simpa using NonUnitalStarAlgHom.norm_apply_le tC.functional.gnsStarAlgHom x))) (hd a)
    rintro _ ⟨x,rfl⟩
    have hm : inc x ∈ iSup R := by
      obtain ⟨y,hy,hxy⟩ := hinc x.property
      have heq : y=inc x := Subtype.ext hxy
      exact heq ▸ hy
    exact Set.subset_centralizer_centralizer ⟨inc x,hm,rfl⟩
  let eC : C := ⟨e,StarSubalgebra.le_topologicalClosure _ ((le_iSup S i) he_mem)⟩
  let bC : C := ⟨b,StarSubalgebra.le_topologicalClosure _ ((le_iSup S j) hb_mem)⟩
  have heC : IsStarProjection eC := ⟨by apply Subtype.ext; exact he.isIdempotentElem,
    by apply Subtype.ext; exact he.isSelfAdjoint⟩
  have hbC : IsSelfAdjoint bC := by apply Subtype.ext; exact hb
  have h := free_compression_norm tC R hR hij heC he_mem hbC hb_mem hb0 hgen
  have hn : ‖tC.functional.toPreGNS bC‖=‖t.functional.toPreGNS b‖ := by
    rw [PositiveLinearMap.preGNS_norm_def,PositiveLinearMap.preGNS_norm_def]
    rfl
  rw [hn] at h
  exact h

end Kadison.FreeCreation

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeFejerNorm
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open scoped ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

include hd0 hpform in
lemma half_projection_trace : t.functional p=((1/2:ℝ):ℂ) := by
  rw [hpform,map_smul,map_add,t.normalized,hd0,add_zero,smul_eq_mul,mul_one]
  norm_num

lemma halfCornerState_linear (hpt : t.functional p=((1/2:ℝ):ℂ)) :
    (halfCornerState t hp hpt).functional.toLinearMap=halfCornerTrace hp t.functional.toLinearMap := by
  ext a
  change (1/2:ℝ)⁻¹ • t.functional (a:A)=2*t.functional (a:A)
  norm_num [Complex.real_smul]

include hfree htr hd hs hd0 hs0 hr hd2 hpform hpd hdp in
theorem free_fejer_norm_oai (e : Corner hp) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD) (m : ℕ) (hm : 0 < m) :
    ‖(e:A)*((fejerCorner hp (d*s) m:Corner hp):A)*(e:A)‖≤
      4*Real.sqrt 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
        Real.sqrt ((m:ℝ)⁻¹)+2*(halfCornerTrace hp t.functional.toLinearMap e).re := by
  let tc := halfCornerState t hp (half_projection_trace t d hd0 hpform)
  let R := cornerPairFactors (S:=S) d s false hr hp hpform hdp hpD
  have hR : Free R tc.functional.toLinearMap := by
    rw [halfCornerState_linear]
    exact corner_cosine_free t.functional.toLinearMap t.normalized htr
      (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hp hpform hpd hdp hpD
  have heR : e∈R false := he
  have hbR : fejerCorner hp (d*s) m∈R true := fejerCorner_mem hp (d*s) d hr hpform hdp m
  have hb0 : tc.functional (fejerCorner hp (d*s) m)=0 := by
    change tc.functional.toLinearMap (fejerCorner hp (d*s) m)=0
    rw [halfCornerState_linear]
    exact fejerCorner_centered hp t.functional S t.normalized htr
      (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
      hd hs hd0 hs0 hr hd2 hpform m hm
  have hn := FreeCreation.free_compression_norm_intrinsic tc R hR Bool.false_ne_true
    heproj heR (fejerCorner_selfAdjoint hp (d*s) m) hbR hb0
  have htce : tc.functional e = halfCornerTrace hp t.functional.toLinearMap e :=
    congrArg (fun f : Corner hp →ₗ[ℂ] ℂ => f e) (halfCornerState_linear t hp _)
  rw [htce] at hn
  have hu : 0≤(halfCornerTrace hp t.functional.toLinearMap e).re := by
    rw [←htce,←FreeCreation.norm_preGNS_projection_sq tc heproj]
    positivity
  have hb2 := fejerCorner_preGNS_norm hp t.functional S t.normalized htr
    (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
    hd hs hd0 hs0 hr hpform m hm
  have hbnorm := fejerCorner_norm_le hp (d*s) m hm
  change ‖e*fejerCorner hp (d*s) m*e‖≤_
  calc
    _ ≤ 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
        ‖tc.functional.toPreGNS (fejerCorner hp (d*s) m)‖+
        (halfCornerTrace hp t.functional.toLinearMap e).re*‖fejerCorner hp (d*s) m‖ := hn
    _ ≤ 2*Real.sqrt (halfCornerTrace hp t.functional.toLinearMap e).re*
        (2*Real.sqrt 2*Real.sqrt ((m:ℝ)⁻¹))+
        (halfCornerTrace hp t.functional.toLinearMap e).re*2 :=
      add_le_add (mul_le_mul_of_nonneg_left hb2 (by positivity))
        (mul_le_mul_of_nonneg_left hbnorm hu)
    _ = _ := by ring

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.free_fejer_norm_oai := @OAI.Kadison.FreeBlocks.free_fejer_norm_oai
