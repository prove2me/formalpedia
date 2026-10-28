-- Prove2me | solution 1 for OAI.Kadison.DihedralCorner.compression_symmetry_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:54:19.912126+00:00
-- url     : https://prove2.me/submissions/f151ae1e-1d08-4ff1-8edc-4d2f5339ba18

import Mathlib
import Definitions.Def_OAIQ039C059

section
-- module Solutions.OAIQ039_CM.Commutator_AlgebraFreeExpectation
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

namespace Kadison.AlgebraFreeExpectation

open FreeMoments

variable {A : Type*} [Ring A] [Algebra ℂ A] [StarRing A] [StarModule ℂ A]

variable (τ : A →ₗ[ℂ] ℂ) (hτ1 : τ 1=1) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (hfree : Free S τ)

lemma centered_mem {i : ι} {a : A} (ha : a ∈ S i) :
    a - τ a • (1 : A) ∈ S i :=
  sub_mem ha (SMulMemClass.smul_mem _ (one_mem (S i)))

omit [StarRing A] [StarModule ℂ A] in
include hτ1 in
lemma centered_zero (a : A) : τ (a - τ a • (1 : A)) = 0 := by
  simp [map_sub, map_smul, hτ1]

include hfree in
lemma free_two {i j : ι} (hij : i ≠ j) {a b : A} (ha : a ∈ S i) (hb : b ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0) :
    τ (a*b) = 0 := by
  let x : Letter S τ := ⟨i, a, ha, ha0⟩
  let y : Letter S τ := ⟨j, b, hb, hb0⟩
  have h := hfree [x, y] (by simpa [Reduced, List.isChain_cons_cons, x, y]) (by simp)
  simpa [word, x, y] using h

include hfree in
lemma free_three {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i)
    (ha0 : τ a = 0) (hb0 : τ b = 0) (hc0 : τ c = 0) :
    τ (a*b*c) = 0 := by
  let x : Letter S τ := ⟨i, a, ha, ha0⟩
  let y : Letter S τ := ⟨j, b, hb, hb0⟩
  let z : Letter S τ := ⟨i, c, hc, hc0⟩
  have h := hfree [x, y, z]
    (by simp [Reduced, List.isChain_cons_cons, x, y, z, hij, hij.symm]) (by simp)
  simpa [word, x, y, z, mul_assoc] using h

include hfree in
lemma free_four {i j : ι} (hij : i ≠ j) {a b c d : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S i) (hd : d ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0)
    (hc0 : τ c = 0) (hd0 : τ d = 0) :
    τ (a*b*c*d) = 0 := by
  let x : Letter S τ := ⟨i, a, ha, ha0⟩
  let y : Letter S τ := ⟨j, b, hb, hb0⟩
  let z : Letter S τ := ⟨i, c, hc, hc0⟩
  let w : Letter S τ := ⟨j, d, hd, hd0⟩
  have h := hfree [x, y, z, w]
    (by simp [Reduced, List.isChain_cons_cons, x, y, z, w, hij, hij.symm]) (by simp)
  simpa [word, x, y, z, w, mul_assoc] using h

include hτ1 hfree in
lemma mul_centered_zero {i j : ι} (hij : i ≠ j) {a b : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hb0 : τ b = 0) :
    τ (a*b) = 0 := by
  have h := free_two τ S hfree hij (centered_mem τ S ha) hb (centered_zero τ hτ1 a) hb0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hb0] using h

include hτ1 hfree in
lemma centered_middle_pairing {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0) :
    τ (c*a*b) = 0 := by
  have h := free_three τ S hfree hij.symm (centered_mem τ S hc) ha hb
    (centered_zero τ hτ1 c) ha0 hb0
  have hab := free_two τ S hfree hij ha hb ha0 hb0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hab, mul_assoc] using h

include hτ1 hfree in
lemma centered_sandwich_pairing {i j : ι} (hij : i ≠ j) {a b c : A}
    (ha : a ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j)
    (ha0 : τ a = 0) (hb0 : τ b = 0) :
    τ (c*a*b*a) = 0 := by
  have h := free_four τ S hfree hij.symm (centered_mem τ S hc) ha hb ha
    (centered_zero τ hτ1 c) ha0 hb0 ha0
  have hab := free_three τ S hfree hij ha hb ha ha0 hb0 ha0
  simpa [sub_mul, smul_mul_assoc, map_sub, map_smul, hab] using h

include hτ1 hfree in
theorem free_compression_pairing {i j : ι} (hij : i ≠ j) {e b c : A}
    (he : e ∈ S i) (hb : b ∈ S j) (hc : c ∈ S j) (hb0 : τ b = 0) :
    τ (c * (e*b*e)) = (τ e)^2 * τ (c*b) := by
  let a := e - τ e • (1 : A)
  have ha : a ∈ S i := centered_mem τ S he
  have ha0 : τ a = 0 := centered_zero τ hτ1 e
  have h1 := centered_sandwich_pairing τ hτ1 S hfree hij ha hb hc ha0 hb0
  have h2 := centered_middle_pairing τ hτ1 S hfree hij ha hb hc ha0 hb0
  have h3 := mul_centered_zero τ hτ1 S hfree hij.symm (mul_mem hc hb) ha ha0
  have hid : c * (e*b*e) = c*a*b*a + τ e • (c*a*b) +
      τ e • (c*b*a) + ((τ e)^2) • (c*b) := by
    dsimp [a]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, mul_one,
      smul_sub, smul_smul, pow_two]
    noncomm_ring
  rw [hid]
  simp only [map_add, map_smul, h1, h2, h3, smul_eq_mul, mul_zero, zero_add]

end Kadison.AlgebraFreeExpectation

end

end
end

end OAI
end

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
-- module Solutions.OAIQ039_CM.Commutator_DihedralCompressionMoments
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

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d : A)*(d : A)=1)

variable {p : A} (hp : IsStarProjection p) (hpform : p=(1/2 : ℂ) • (1+(d : A)))
  (hpd : p*(d : A)=p) (hdp : (d : A)*p=p)

include htr in
lemma corner_wave_pairing (u : unitary A) (n : ℤ) (b : Corner hp) :
    halfCornerTrace hp τ (cosine u hp n*b)=2*τ (wave u n*(b:A)) := by
  rw [halfCornerTrace_apply,corner_mul,cosine_coe]
  congr 1
  calc
    τ ((p*wave u n*p)*(b:A)) = τ (p*(wave u n*(b:A))) := by
      simp only [mul_assoc,b.property.1]
    _ = τ ((wave u n*(b:A))*p) := htr _ _
    _ = τ (wave u n*(b:A)) := by rw [mul_assoc,b.property.2]

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
theorem free_compression_wave_pairing (hpD : p∈S i) (e b : Corner hp)
    (he : e∈cornerFactor hp (S i) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) (n : ℤ) :
    τ (wave (d*s) n*((e:A)*(b:A)*(e:A)))=
      (halfCornerTrace hp τ e)^2*τ (wave (d*s) n*(b:A)) := by
  let R := cornerPairFactors (S:=S) d s i hr hp hpform hdp hpD
  have hR := corner_cosine_free τ h1 htr hstar hfree d s i j hij hd hs hd0 hs0
    hr hd2 hp hpform hpd hdp hpD
  have hn : cosine (d*s) hp n∈R true := cosine_mem (d*s) hp n
  have hz := AlgebraFreeExpectation.free_compression_pairing (halfCornerTrace hp τ)
    (halfCornerTrace_one τ h1 d hd0 hp hpform) R hR Bool.false_ne_true he hb hn hb0
  rw [corner_wave_pairing τ htr hp,corner_wave_pairing τ htr hp] at hz
  change 2*τ (wave (d*s) n*((e:A)*(b:A)*(e:A)))=
    (halfCornerTrace hp τ e)^2*(2*τ (wave (d*s) n*(b:A))) at hz
  linear_combination (1/2:ℂ)*hz

include hdp in
lemma reflection_corner (x : Corner hp) : (d:A)*(x:A)=(x:A) := by
  calc
    (d:A)*(x:A) = (d:A)*(p*(x:A)) := by rw [x.property.1]
    _ = (d:A)*p*(x:A) := (mul_assoc _ _ _).symm
    _ = (x:A) := by rw [hdp,x.property.1]

include hd2 in
lemma symmetry_wave_product (a : ℤ) : (s:A)*wave (d*s) a=
    (d:A)*wave (d*s) (a+1) := by
  have hw : wave (d*s) (a+1)=((d:A)*(s:A))*wave (d*s) a := by
    rw [add_comm a 1,wave_add]
    simp only [wave,zpow_one,Submonoid.coe_mul]
  rw [hw,←mul_assoc,←mul_assoc,hd2,one_mul]

include htr hr hd2 hdp in
lemma symmetry_sandwich_trace (x : Corner hp) (a b : ℤ) :
    τ ((s:A)*(wave (d*s) a*(x:A)*wave (d*s) (-b)))=
      τ (wave (d*s) (-(a+b+1))*(x:A)) := by
  calc
    _ = τ (wave (d*s) (-b)*((s:A)*wave (d*s) a)*(x:A)) := by
      rw [←mul_assoc (s:A),htr]
      simp only [mul_assoc]
    _ = τ (wave (d*s) (-b)*((d:A)*wave (d*s) (a+1))*(x:A)) := by
      rw [symmetry_wave_product d s hd2]
    _ = τ (wave (d*s) (-b)*(wave (d*s) (-(a+1))*(d:A))*(x:A)) := by
      rw [reflection_wave (d*s) d hr]
    _ = τ ((wave (d*s) (-b)*wave (d*s) (-(a+1)))*((d:A)*(x:A))) := by
      simp only [mul_assoc]
    _ = τ (wave (d*s) (-b+-(a+1))*(x:A)) := by
      rw [reflection_corner d hp hdp,←wave_add]
    _ = _ := by congr 2; congr 1; omega

include htr hr hpd hdp in
lemma wave_corner_even (x : Corner hp) (n : ℤ) :
    τ (wave (d*s) (-n)*(x:A))=τ (wave (d*s) n*(x:A)) := by
  have h := congrArg (fun z : Corner hp => halfCornerTrace hp τ (z*x))
    (cosine_neg (d*s) d hr hp hpd hdp n)
  rw [corner_wave_pairing τ htr hp,corner_wave_pairing τ htr hp] at h
  linear_combination (1/2:ℂ)*h

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hpd in
lemma compression_symmetry_sandwich_oai (hpD : p∈S i) (e b : Corner hp)
    (he : e∈cornerFactor hp (S i) hpD)
    (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
    (hb0 : halfCornerTrace hp τ b=0) (a c : ℤ) :
    τ ((s:A)*(wave (d*s) a*((e:A)*(b:A)*(e:A))*wave (d*s) (-c)))=
      (halfCornerTrace hp τ e)^2*τ (wave (d*s) (a+c+1)*(b:A)) := by
  change τ ((s:A)*(wave (d*s) a*((e*b*e:Corner hp):A)*wave (d*s) (-c)))=_
  rw [symmetry_sandwich_trace τ htr d s hr hd2 hp hdp]
  simp only [corner_mul]
  rw [free_compression_wave_pairing τ h1 htr hstar hfree d s i j hij hd hs hd0 hs0
    hr hd2 hp hpform hpd hdp hpD e b he hb hb0]
  rw [wave_corner_even τ htr d s hr hp hpd hdp]

end Kadison.DihedralCorner

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.DihedralCorner.compression_symmetry_sandwich_oai.{u_1, u_2} := @OAI.Kadison.DihedralCorner.compression_symmetry_sandwich_oai.{u_1, u_2}
