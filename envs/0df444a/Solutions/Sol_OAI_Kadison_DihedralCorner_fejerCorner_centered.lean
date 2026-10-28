-- Prove2me | solution 1 for OAI.Kadison.DihedralCorner.fejerCorner_centered
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:54:20.891346+00:00
-- url     : https://prove2.me/submissions/936c2c4a-22e5-4ede-95ac-a6d451b6127b

import Mathlib
import Definitions.Def_OAIQ039C059

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

end Kadison.FreeMoments

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

include hfree hij hd hs hd0 hs0 in
lemma wave_positive_trace (n : ℕ) : τ (wave (d*s) ((n+1:ℕ):ℤ))=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have h := alternating_power_centered hfree D F hij n
  change τ (((d:A)*(s:A))^(n+1))=0 at h
  simpa only [wave_nat,Submonoid.coe_mul] using h

include hstar hfree hij hd hs hd0 hs0 in
lemma wave_trace_zero (n : ℤ) (hn : n≠0) : τ (wave (d*s) n)=0 := by
  cases n with
  | ofNat n =>
      cases n with
      | zero => exact (hn rfl).elim
      | succ n => exact wave_positive_trace τ hfree d s i j hij hd hs hd0 hs0 n
  | negSucc n =>
      change τ (wave (d*s) (-((n+1:ℕ):ℤ)))=0
      rw [←wave_star,hstar,wave_positive_trace τ hfree d s i j hij hd hs hd0 hs0,star_zero]

include h1 hstar hfree hij hd hs hd0 hs0 in
lemma wave_trace (n : ℤ) : τ (wave (d*s) n)=if n=0 then 1 else 0 := by
  split_ifs with h
  · simp [h,h1]
  · exact wave_trace_zero τ hstar hfree d s i j hij hd hs hd0 hs0 n h

include h1 hstar hfree hij hd hs hd0 hs0 in
theorem dihedral_haar (a b : ℕ) :
    τ (star (((d:A)*(s:A))^a)*((d:A)*(s:A))^b)=if a=b then 1 else 0 := by
  have hw (m : ℕ) : ((d:A)*(s:A))^m=wave (d*s) (m:ℤ) := (wave_nat (d*s) m).symm
  rw [hw a,hw b,wave_star,←wave_add,wave_trace τ h1 hstar hfree d s i j hij hd hs hd0 hs0]
  have he : (-(a:ℤ)+(b:ℤ)=0) ↔ a=b := by omega
  simp only [he]

include hfree hij hd hs hd0 hs0 in
lemma reflection_positive_trace (n : ℕ) : τ (wave (d*s) (n:ℤ)*(d:A))=0 := by
  let D : Letter S τ := ⟨i,d,hd,hd0⟩
  let F : Letter S τ := ⟨j,s,hs,hs0⟩
  have h := alternating_odd_centered hfree F D hij.symm n
  have hm : ((d:A)*(s:A))^n*(d:A)=(d:A)*((s:A)*(d:A))^n := by
    exact mul_pow_mul (d:A) (s:A) n
  rw [wave_nat]
  change τ (((d:A)*(s:A))^n*(d:A))=0
  rw [hm]
  exact h

lemma symmetry_star (u : unitary A) (hu : (u:A)*(u:A)=1) : star (u:A)=(u:A) := by
  have h := congrArg ((star (u:A)) * ·) hu
  simpa only [←mul_assoc,Unitary.coe_star_mul_self,one_mul,mul_one] using h.symm

include htr hstar hfree hij hd hs hd0 hs0 in
lemma reflection_trace (hd2 : (d:A)*(d:A)=1) (n : ℤ) :
    τ (wave (d*s) n*(d:A))=0 := by
  cases n with
  | ofNat n => exact reflection_positive_trace τ hfree d s i j hij hd hs hd0 hs0 n
  | negSucc n =>
    change τ (wave (d*s) (-((n+1:ℕ):ℤ))*(d:A))=0
    calc
      _ = τ ((d:A)*wave (d*s) (-((n+1:ℕ):ℤ))) := htr _ _
      _ = τ (star (wave (d*s) ((n+1:ℕ):ℤ)*(d:A))) := by
        rw [star_mul,symmetry_star d hd2,wave_star]
      _ = star (τ (wave (d*s) ((n+1:ℕ):ℤ)*(d:A))) := hstar _
      _ = 0 := by rw [reflection_positive_trace τ hfree d s i j hij hd hs hd0 hs0,star_zero]

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

lemma triangular_count (m l : ℕ) :
    (∑ j ∈ Finset.range m, ∑ i ∈ Finset.range m,
      if i = j+l then (1 : ℂ) else 0) = ((m-l : ℕ) : ℂ) := by
  have hs (j : ℕ) : (∑ i ∈ Finset.range m, if i = j+l then (1 : ℂ) else 0) =
      if j+l < m then 1 else 0 := by simp [Finset.mem_range]
  simp only [hs]
  have he : ∀ j : ℕ, j+l < m ↔ j < m-l := by omega
  simp only [he]
  rw [← Finset.sum_filter]
  have hf : (Finset.range m).filter (fun j => j < m-l) = Finset.range (m-l) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  simp [hf]

variable {A : Type*} [CStarAlgebra A]

variable [PartialOrder A] [StarOrderedRing A]

variable (φ : A →ₚ[ℂ] ℂ) (w : A)

variable (hhaar : HaarMoments φ w)

include hhaar

omit [StarOrderedRing A] in
lemma moment_square_shift (m l : ℕ) :
    φ (star (powerAverage w m) * powerAverage w m * w^l) =
      (m : ℂ)⁻¹ * (m : ℂ)⁻¹ * ((m-l : ℕ) : ℂ) := by
  change ∀ i j : ℕ, φ (star (w^i) * w^j) = if i=j then 1 else 0 at hhaar
  have hs : star ((m : ℂ)⁻¹) = (m : ℂ)⁻¹ := by simp
  simp only [powerAverage, star_smul, hs, star_sum,
    smul_mul_assoc, mul_smul_comm, Finset.sum_mul, Finset.mul_sum, map_smul,
    map_sum, smul_eq_mul, mul_assoc, ← pow_add, hhaar]
  simp only [← Finset.mul_sum, ← mul_assoc]
  rw [triangular_count]

omit [StarOrderedRing A] in
lemma moment_square (m : ℕ) (hm : 0 < m) :
    φ (star (powerAverage w m) * powerAverage w m) = (m : ℂ)⁻¹ := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simpa [hm'] using moment_square_shift φ w hhaar m 0

omit [StarOrderedRing A] in
lemma moment_testPolynomial (h1 : φ 1 = 1) (m : ℕ) (hm : 0 < m) :
    φ (testPolynomial w m) = 0 := by
  simp [testPolynomial, moment_square φ w hhaar m hm, h1]

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

lemma testPolynomial_reflection_commute (u d : unitary A)
    (hr : MulAut.conj d u=u⁻¹) (m : ℕ) :
    (d:A)*testPolynomial (u:A) m=testPolynomial (u:A) m*(d:A) := by
  rw [testPolynomial_expansion]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,one_mul]
  congr 1
  congr 1
  simp only [Finset.mul_sum,Finset.sum_mul,reflection_wave u d hr]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  omega

variable {p : A} (hp : IsStarProjection p)

lemma fejerCorner_coe_right (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)
    (hpform : p=(1/2:ℂ) • (1+(d:A))) (m : ℕ) :
    ((fejerCorner hp u m:Corner hp):A)=testPolynomial (u:A) m*p := by
  change p*testPolynomial (u:A) m*p=_
  have comm : p*testPolynomial (u:A) m=testPolynomial (u:A) m*p := by
    rw [hpform]
    simp only [smul_mul_assoc,mul_smul_comm,add_mul,mul_add,one_mul,mul_one,
      testPolynomial_reflection_commute u d hr]
  rw [comm,mul_assoc,hp.isIdempotentElem.eq]

variable [PartialOrder A] [StarOrderedRing A]

variable (φ : A →ₚ[ℂ] ℂ) {ι : Type*} (S : ι → StarSubalgebra ℂ A)

variable (h1 : φ 1=1) (htr : ∀ a b : A, φ (a*b)=φ (b*a))
  (hstar : ∀ a : A, φ (star a)=star (φ a)) (hfree : Free S φ.toLinearMap)

variable (d s : unitary A) (i j : ι) (hij : i≠j)

variable (hd : (d:A)∈S i) (hs : (s:A)∈S j)
  (hd0 : φ (d:A)=0) (hs0 : φ (s:A)=0)

variable (hr : MulAut.conj d (d*s)=(d*s)⁻¹) (hd2 : (d:A)*(d:A)=1)

variable (hpform : p=(1/2:ℂ) • (1+(d:A)))

include htr hstar hfree hij hd hs hd0 hs0 hd2 in
omit [StarOrderedRing A] in
lemma testPolynomial_reflection_trace (m : ℕ) (l : ℤ) :
    φ (wave (d*s) l*testPolynomial ((d*s:unitary A):A) m*(d:A))=0 := by
  have ht (n : ℤ) : φ (wave (d*s) n*(d:A))=0 :=
    reflection_trace φ.toLinearMap htr hstar hfree d s i j hij hd hs hd0 hs0 hd2 n
  rw [testPolynomial_expansion]
  simp only [mul_sub,sub_mul,mul_smul_comm,smul_mul_assoc,mul_one,
    Finset.mul_sum,Finset.sum_mul,←wave_add,map_sub,map_smul,map_sum,
    ht,
    smul_zero,Finset.sum_const_zero,sub_zero]

include htr hstar hfree hij hd hs hd0 hs0 hd2 hr hpform in
omit [StarOrderedRing A] in
lemma fejerCorner_wave_trace (m : ℕ) (l : ℤ) :
    φ (wave (d*s) l*((fejerCorner hp (d*s) m:Corner hp):A))=
      (1/2:ℂ)*φ (testPolynomial ((d*s:unitary A):A) m*wave (d*s) l) := by
  rw [fejerCorner_coe_right hp (d*s) d hr hpform]
  let q := testPolynomial ((d*s:unitary A):A) m
  have he : wave (d*s) l*(q*p)=(1/2:ℂ) •
      (wave (d*s) l*q + wave (d*s) l*q*(d:A)) := by
    rw [hpform]
    simp only [mul_smul_comm,mul_add,mul_one,mul_assoc]
  rw [he]
  simp only [map_smul,map_add,smul_eq_mul]
  rw [testPolynomial_reflection_trace φ S htr hstar hfree d s i j hij
    hd hs hd0 hs0 hd2,add_zero,htr]

include h1 htr hstar hfree hij hd hs hd0 hs0 hd2 hr hpform in
omit [StarOrderedRing A] in
lemma fejerCorner_centered_oai (m : ℕ) (hm : 0 < m) :
    halfCornerTrace hp φ.toLinearMap (fejerCorner hp (d*s) m)=0 := by
  have hhaar : HaarMoments φ ((d*s:unitary A):A) :=
    dihedral_haar φ.toLinearMap h1 hstar hfree d s i j hij hd hs hd0 hs0
  have h := fejerCorner_wave_trace hp φ S htr hstar hfree d s i j hij
    hd hs hd0 hs0 hr hd2 hpform m 0
  simp only [wave_zero,one_mul,mul_one,moment_testPolynomial φ _ hhaar h1 m hm,
    mul_zero] at h
  simp only [halfCornerTrace_apply,PositiveLinearMap.coe_toLinearMap,h,mul_zero]

end Kadison.DihedralCorner

end

end
end

end OAI
end

theorem solution.{u_1, u_2} : type_of% @OAI.Kadison.DihedralCorner.fejerCorner_centered_oai.{u_1, u_2} := @OAI.Kadison.DihedralCorner.fejerCorner_centered_oai.{u_1, u_2}
