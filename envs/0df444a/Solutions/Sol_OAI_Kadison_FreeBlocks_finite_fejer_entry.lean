-- Prove2me | solution 1 for OAI.Kadison.FreeBlocks.finite_fejer_entry
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T10:59:32.780776+00:00
-- url     : https://prove2.me/submissions/d9ef400f-b6f0-4043-af52-9c8a5c95acf3

import Mathlib
import Definitions.Def_OAIQ039C059
import Theorems.Thm_OAI_Kadison_DihedralCorner_fejerCorner_centered
import Theorems.Thm_OAI_Kadison_FreeBlocks_dihedral_entry_pairing

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
lemma moment_power (l : ℕ) : φ (w^l) = if l=0 then 1 else 0 := by
  simpa [eq_comm] using hhaar 0 l

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
lemma positive_coefficient (m l : ℕ) (hm : 0 < m)
    (hl : 0 < l) (hlm : l < m) :
    φ (testPolynomial w m * w^l) = ((m : ℂ) - (l : ℂ)) / (m : ℂ)^2 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  simp only [testPolynomial, sub_mul, smul_mul_assoc, one_mul, map_sub, map_smul,
    moment_square_shift φ w hhaar, moment_power φ w hhaar,
    ite_eq_right (Nat.ne_of_gt hl), smul_zero, sub_zero]
  rw [Nat.cast_sub (Nat.le_of_lt hlm)]
  field_simp

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

lemma fejerCorner_mem (u d : unitary A) (hr : MulAut.conj d u=u⁻¹)
    (hpform : p=(1/2:ℂ) • (1+(d:A))) (hdp : (d:A)*p=p) (m : ℕ) :
    fejerCorner hp u m∈cosineAlgebra u d hr hp hpform hdp := by
  let R := cosineAlgebra u d hr hp hpform hdp
  unfold fejerCorner
  rw [testPolynomial_expansion]
  simp only [map_sub,map_smul,map_sum,compressCorner_wave,compressCorner_one]
  exact R.sub_mem (R.smul_mem (R.sum_mem (fun i _ =>
    R.sum_mem (fun j _ => cosine_mem u hp _))) _) (R.smul_mem R.one_mem _)

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
lemma fejerCorner_positive_coefficient (m l : ℕ) (hm : 0 < m)
    (hl : 0 < l) (hlm : l < m) :
    2*φ (wave (d*s) (l:ℤ)*((fejerCorner hp (d*s) m:Corner hp):A))=
      ((m:ℂ)-(l:ℂ))/(m:ℂ)^2 := by
  rw [fejerCorner_wave_trace hp φ S htr hstar hfree d s i j hij
    hd hs hd0 hs0 hr hd2 hpform, wave_nat]
  have hhaar : HaarMoments φ ((d*s:unitary A):A) :=
    dihedral_haar φ.toLinearMap h1 hstar hfree d s i j hij hd hs hd0 hs0
  rw [positive_coefficient φ _ hhaar m l hm hl hlm]
  ring

end Kadison.DihedralCorner

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeHilbertEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

lemma base_operator_ext
    (T R : multiplicityLevel t S true 0 →L[ℂ] multiplicityLevel t S true 0)
    (h : ∀ v z : factorSpace t S true,
      inner ℂ (z : multiplicityLevel t S true 0) (T (v : multiplicityLevel t S true 0))=
      inner ℂ (z : multiplicityLevel t S true 0) (R (v : multiplicityLevel t S true 0))) : T=R := by
  ext v
  apply ext_inner_left ℂ
  intro z
  induction v,z using Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih v z => exact h v z

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeDihedralEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped InnerProductSpace ComplexOrder

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

variable {A : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

lemma base_compression_of_entries
    (U V : multiplicityLevel t S true 0 →L[ℂ] t.functional.GNS)
    (L : t.functional.GNS →L[ℂ] t.functional.GNS)
    (α β γ : ℂ) (R : multiplicityLevel t S true 0 →L[ℂ] multiplicityLevel t S true 0)
    (hh : ∀ v z : factorSpace t S true,
      inner ℂ (U (z : multiplicityLevel t S true 0))
        (L (V (v : multiplicityLevel t S true 0)))=
      α*(β*inner ℂ (z : multiplicityLevel t S true 0) (v : multiplicityLevel t S true 0)+
        γ*inner ℂ (z : multiplicityLevel t S true 0) (R (v : multiplicityLevel t S true 0)))) :
    (ContinuousLinearMap.adjoint (E := multiplicityLevel t S true 0) (F := t.functional.GNS) U).comp
      (L.comp V)=α • (β • ContinuousLinearMap.id ℂ (multiplicityLevel t S true 0)+γ • R) := by
  apply base_operator_ext t S
  intro v z
  dsimp only [ContinuousLinearMap.comp_apply]
  rw [ContinuousLinearMap.adjoint_inner_right
    (E := multiplicityLevel t S true 0) (F := t.functional.GNS)]
  change inner ℂ (U (z : multiplicityLevel t S true 0))
    (L (V (v : multiplicityLevel t S true 0)))=
    inner ℂ (z : Completion (factorSpace t S true))
      (α • (β • (v : Completion (factorSpace t S true))+
        γ • R (v : multiplicityLevel t S true 0)))
  rw [inner_smul_right (𝕜 := ℂ) (E := Completion (factorSpace t S true)),inner_add_right (𝕜 := ℂ) (E := Completion (factorSpace t S true)),
    inner_smul_right (𝕜 := ℂ) (E := Completion (factorSpace t S true)),inner_smul_right (𝕜 := ℂ) (E := Completion (factorSpace t S true))]
  exact hh v z

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hr : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable {p : A} (hp : IsStarProjection p)
  (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

variable (e b : Corner hp) (he : e∈cornerFactor hp (S false) hpD)
  (hb : b∈cosineAlgebra (d*s) d hr hp hpform hdp)
  (hb0 : halfCornerTrace hp t.functional.toLinearMap b=0)

omit [PartialOrder A] [StarOrderedRing A] in
lemma corner_projection_coe (heproj : IsStarProjection e) : IsStarProjection (e:A) where
  isSelfAdjoint := by
    show star (e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isSelfAdjoint.star_eq
  isIdempotentElem := by
    show (e:A)*(e:A)=(e:A)
    exact congrArg (fun a : Corner hp => (a:A)) heproj.isIdempotentElem.eq

include htr hd hs hd0 hs0 hd2 hs2 hpd he hb hb0 in
theorem dihedral_entry_operator (heproj : IsStarProjection e)
    (c : ℝ) (n m : ℕ) :
    (ContinuousLinearMap.adjoint (E := multiplicityLevel t S true 0) (F := t.functional.GNS)
      (dihedralColumn t S hfree (e:A) (d*s) c n)).comp
      ((t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A))).comp
        (dihedralColumn t S hfree (e:A) (d*s) c m))=
    ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2) •
      (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A)) •
          ContinuousLinearMap.id ℂ (multiplicityLevel t S true 0)+
       t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A)) • baseAction t S hfree (s:A)) := by
  exact base_compression_of_entries t S
    (dihedralColumn t S hfree (e:A) (d*s) c n)
    (dihedralColumn t S hfree (e:A) (d*s) c m)
    (t.functional.gnsStarAlgHom ((e:A)*(b:A)*(e:A)))
    ((c:ℂ)^2*(halfCornerTrace hp t.functional.toLinearMap e)^2)
    (t.functional (wave (d*s) ((n:ℤ)-m)*(b:A)))
    (t.functional (wave (d*s) ((n:ℤ)+m+1)*(b:A)))
    (baseAction t S hfree (s:A))
    (dihedral_entry_pairing t S hfree htr d s hd hs hd0 hs0 hr hd2 hs2
      hp hpform hpd hdp hpD e b he hb hb0 heproj c n m)

end Kadison.FreeBlocks

end

end
end

end OAI
end

section
-- module Solutions.OAIQ039_CM.Commutator_FreeHankelEntries
attribute [-instance] _root_.OAI.Kadison.ConcreteCorner.closedCarrier _root_.OAI.Kadison.CyclicColumns.instDecidableEq_solutions _root_.OAI.Kadison.UnitaryDualAction.action _root_.OAI.Kadison.VonNeumannCStar.cstarAlgebra _root_.OAI.Kadison.VonNeumannCStar.isClosed _root_.OAI.Kadison.VonNeumannCStar.smulMemClass _root_.OAI.Kadison.VonNeumannCStar.starOrderedRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

section

noncomputable section

open UniformSpace

open scoped ComplexOrder InnerProductSpace

namespace Kadison.FreeBlocks

open FreeMoments FreeWordTensor DihedralCorner

lemma two_scaled_sum {M : Type*} [AddCommGroup M] [Module ℂ M]
    (u a b c : ℂ) (x y : M) (hc : 2*b=c) :
    (2*u) • (a • x+b • y)=u • ((2*a) • x+c • y) := by
  rw [←hc]
  module

variable {A D : Type} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [CStarAlgebra D] [PartialOrder D] [StarOrderedRing D]

variable (t : FaithfulState A) (S : Bool → StarSubalgebra ℂ A)
  (hfree : Free S t.functional.toLinearMap)

variable (f : D →⋆ₐ[ℂ] A) (hf : Function.Injective f)

variable {p : A} (hp : IsStarProjection p)

lemma projection_factor_trace (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    t.functional (e:A)=((‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2:ℝ):ℂ) := by
  have hn := (factorTrace t f hf).preGNS_norm_sq ((factorTrace t f hf).toPreGNS e0)
  have he := corner_projection_coe hp (e:=e) heproj
  symm
  simpa only [TracialGNS.algebraVector_apply,Completion.norm_coe,
    Complex.ofReal_pow,PositiveLinearMap.ofPreGNS_toPreGNS,pullbackState_apply,
    map_mul,map_star,heq,he.isSelfAdjoint.star_eq,he.isIdempotentElem.eq] using hn

lemma halfCornerTrace_normalization (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e) :
    halfCornerTrace hp t.functional.toLinearMap e=
      ((2*‖TracialGNS.algebraVector (factorTrace t f hf) e0‖^2:ℝ):ℂ) := by
  rw [halfCornerTrace_apply,PositiveLinearMap.coe_toLinearMap,
    projection_factor_trace t f hf hp e0 e heq heproj]
  push_cast
  rfl

lemma normalized_dihedral_scalar (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖) :
    (((‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹:ℝ):ℂ)^2 *
      (halfCornerTrace hp t.functional.toLinearMap e)^2)=
      2*((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) := by
  rw [halfCornerTrace_normalization t f hf hp e0 e heq heproj,Complex.ofReal_re]
  have hn : (‖TracialGNS.algebraVector (factorTrace t f hf) e0‖:ℂ)≠0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
  push_cast
  field_simp

variable (htr : ∀ a b : A, t.functional (a*b)=t.functional (b*a))

variable (d s : unitary A) (hd : (d:A)∈S false) (hs : (s:A)∈S true)
  (hd0 : t.functional (d:A)=0) (hs0 : t.functional (s:A)=0)
  (hrot : MulAut.conj d (d*s)=(d*s)⁻¹)
  (hd2 : (d:A)*(d:A)=1) (hs2 : (s:A)*(s:A)=1)

variable (hpform : p=(1/2:ℂ) • (1+(d:A))) (hpd : p*(d:A)=p) (hdp : (d:A)*p=p)
  (hpD : p∈S false)

include hfree htr hd hs hd0 hs0 hrot hd2 hs2 hpform hpd hdp in
theorem finite_fejer_entry_oai (e0 : D) (e : Corner hp)
    (heq : f e0=(e:A)) (heproj : IsStarProjection e)
    (he : e∈cornerFactor hp (S false) hpD)
    (hr : 0<‖TracialGNS.algebraVector (factorTrace t f hf) e0‖)
    (N : ℕ) (hN : 0 < N) (i j : Fin N) :
    ((ContinuousLinearMap.adjoint (E:=multiplicityLevel t S true 0) (F:=t.functional.GNS)
      (dihedralColumn t S hfree (e:A) (d*s)
      ‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹ i.val)).comp
      (t.functional.gnsStarAlgHom ((e:A)*((fejerCorner hp (d*s) (2*N):Corner hp):A)*(e:A)))).comp
      (dihedralColumn t S hfree (e:A) (d*s)
        ‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹ j.val)=
    ((halfCornerTrace hp t.functional.toLinearMap e).re:ℂ) •
      ((2*t.functional (wave (d*s) ((i.val:ℤ)-j.val)*
        ((fejerCorner hp (d*s) (2*N):Corner hp):A))) •
          ContinuousLinearMap.id ℂ (multiplicityLevel t S true 0)+
       (Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2)) • baseAction t S hfree (s:A)) := by
  have hm : 0 < 2*N := by omega
  have hb := fejerCorner_mem hp (d*s) d hrot hpform hdp (2*N)
  have hb0 := fejerCorner_centered hp t.functional S t.normalized htr
    (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
    hd hs hd0 hs0 hrot hd2 hpform (2*N) hm
  have hentry := dihedral_entry_operator t S hfree htr d s hd hs hd0 hs0 hrot hd2 hs2
    hp hpform hpd hdp hpD e (fejerCorner hp (d*s) (2*N)) he hb hb0 heproj
    ‖TracialGNS.algebraVector (factorTrace t f hf) e0‖⁻¹ i.val j.val
  rw [normalized_dihedral_scalar t f hf hp e0 e heq heproj hr] at hentry
  have hcoef := fejerCorner_positive_coefficient hp t.functional S t.normalized htr
    (fun a => map_star t.functional a) hfree d s false true Bool.false_ne_true
    hd hs hd0 hs0 hrot hd2 hpform (2*N) (i.val+j.val+1) hm (by omega) (by omega)
  have hcoef' : 2*t.functional (wave (d*s) ((i.val:ℤ)+j.val+1)*
      ((fejerCorner hp (d*s) (2*N):Corner hp):A))=
      Complex.ofReal (((2*N:ℝ)-i.val-j.val-1)/(2*N:ℝ)^2) := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
      Complex.ofReal_div,Complex.ofReal_sub,Complex.ofReal_mul,Complex.ofReal_pow,
      Complex.ofReal_ofNat,Complex.ofReal_natCast,Complex.ofReal_one,
      sub_add_eq_sub_sub] using hcoef
  rw [ContinuousLinearMap.comp_assoc,hentry]
  exact two_scaled_sum
    (M:=Completion (factorSpace t S true) →L[ℂ] Completion (factorSpace t S true))
    _ _ _ _ _ _ hcoef'

end Kadison.FreeBlocks

end

end
end

end OAI
end

theorem solution : type_of% @OAI.Kadison.FreeBlocks.finite_fejer_entry_oai := @OAI.Kadison.FreeBlocks.finite_fejer_entry_oai
