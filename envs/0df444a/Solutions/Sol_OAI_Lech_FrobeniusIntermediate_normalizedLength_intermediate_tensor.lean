-- Prove2me | solution 1 for OAI.Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T21:20:10.485407+00:00
-- url     : https://prove2.me/submissions/4cef1d46-21be-48f4-8270-941b825230a8

import Mathlib
import Definitions.Def_OAIQ032L023

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerLengthEq
attribute [-instance] _root_.OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubring_solutions _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.domainAlgebra _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct


namespace Lech.RootTower
variable {A B C : Type*} [CommRing A] [IsReduced A] [CommRing B] [IsReduced B]
  [CommRing C] [IsReduced C] (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP C p]

omit [IsReduced A] [IsReduced B] in
lemma perfectMap_of (f : A →+* B) (a : A) :
    perfectMap p f (PerfectClosure.of A p a) = PerfectClosure.of B p (f a) :=
  PerfectRing.lift_comp_apply _ _ _ _

end Lech.RootTower


end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_FrobeniusIntermediatePowerMap
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
lemma length_eq_of_semilinearEquiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (E : LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S) M N) :
    Module.length R M = Module.length S N := by
  apply WithBot.coe_injective
  rw [Module.coe_length,Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective E.toLinearMap E.bijective)

lemma length_span_eq_of_semilinearEquiv {R S M N : Type*} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (e : R ≃+* S) (E : LinearEquiv (σ' := (e.symm : S →+* R)) (e : R →+* S) M N) (s : Finset M) :
    Module.length R (Submodule.span R (s : Set M)) =
      Module.length S (Submodule.span S ((s.image E : Finset N) : Set N)) := by
  classical
  exact length_eq_of_semilinearEquiv e
    (E.ofSubmodules _ _ (by rw [Submodule.map_span]; simp only [Finset.coe_image]; rfl))
end Lech


namespace Lech.NormalizedLength.Tower
open scoped ENNReal Classical
variable {L : Type*} [CommRing L] (T : Tower L)
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module L M] [Module L N]

lemma finiteLength_eq_iInf_shift (s : Finset M) (d : ℕ) :
    T.finiteLength s = ⨅ n, T.stage s (n+d) := by
  apply le_antisymm
  · exact le_iInf fun n => T.finiteLength_le_stage s (n+d)
  · apply le_iInf
    intro n
    exact (iInf_le _ n).trans (T.stage_antitone s (Nat.le_add_right n d))

 

lemma length_eq_mul_of_stage_shift (E : M ≃ N) (d : ℕ) (c : ℝ≥0∞)
    (hc : c ≠ ⊤)
    (h : ∀ (s : Finset M) (n : ℕ), T.stage (s.image E) (n+d) = c * T.stage s n) :
    T.length N = c * T.length M := by
  have hf (s : Finset M) : T.finiteLength (s.image E) = c * T.finiteLength s := by
    rw [T.finiteLength_eq_iInf_shift _ d]
    simp_rw [h]
    exact (ENNReal.mul_iInf (fun hh => (hc hh).elim)).symm
  apply le_antisymm
  · apply iSup_le
    intro t
    have he : (t.image E.symm).image E = t := by simp only [Finset.image_image]; simp
    rw [← he,hf]
    exact mul_le_mul_right (T.finiteLength_le_length (t.image E.symm)) c
  · rw [length,ENNReal.mul_iSup]
    exact iSup_le fun s => (hf s).symm ▸ T.finiteLength_le_length (s.image E)
end Lech.NormalizedLength.Tower


namespace Lech.RootTower
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped ENNReal Classical
variable (σ k : Type*) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  [Module (PerfectClosure (MvPowerSeries σ k) p) M]
  [Module (PerfectClosure (MvPowerSeries σ k) p) N]

lemma regular_weight_shift (n d : ℕ) :
    (regularTower σ k p).weight (n+d) =
      ((p : ℝ≥0∞)^(d*Fintype.card σ))⁻¹ * (regularTower σ k p).weight n := by
  change ((p : ℝ≥0∞)^((n+d)*Fintype.card σ))⁻¹ = _ * ((p : ℝ≥0∞)^(n*Fintype.card σ))⁻¹
  have hz : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [Nat.add_mul,pow_add,ENNReal.mul_inv (Or.inl (pow_ne_zero _ hz)) (Or.inl (by simp))]
  exact mul_comm _ _

 

theorem normalizedLength_root_equiv (d : ℕ)
    (E : LinearEquiv (σ' := ((iterateFrobeniusEquiv (PerfectClosure (MvPowerSeries σ k) p) p d) : PerfectClosure (MvPowerSeries σ k) p →+* PerfectClosure (MvPowerSeries σ k) p))
      ((iterateFrobeniusEquiv (PerfectClosure (MvPowerSeries σ k) p) p d).symm : PerfectClosure (MvPowerSeries σ k) p →+* PerfectClosure (MvPowerSeries σ k) p) M N) :
    normalizedLength σ k p N = ((p : ℝ≥0∞)^(d*Fintype.card σ))⁻¹ * normalizedLength σ k p M := by
  apply (regularTower σ k p).length_eq_mul_of_stage_shift E.toEquiv d
  · apply ENNReal.inv_ne_top.mpr
    exact pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  · intro s n
    unfold Lech.NormalizedLength.Tower.stage
    rw [regular_weight_shift]
    rw [mul_assoc]
    congr 1
    congr 1
    exact congrArg ENat.toENNReal (Lech.length_span_eq_of_semilinearEquiv
      (rootShiftEquiv (MvPowerSeries σ k) p n d)
      (restrictRootShift (MvPowerSeries σ k) p d E n) s).symm
end Lech.RootTower


namespace Lech.RootTower
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
open scoped ENNReal Classical
variable {P C : Type*} [CommRing P] [CommRing C] [Algebra P C]
  (p : ℕ) [Fact p.Prime] [CharP P p] [CharP C p] [PerfectRing P p] [PerfectRing C p]

omit [Algebra P C] in
lemma map_inverse_frobenius (f : P →+* C) (d : ℕ) (x : P) :
    f ((iterateFrobeniusEquiv P p d).symm x) =
      (iterateFrobeniusEquiv C p d).symm (f x) := by
  apply (iterateFrobeniusEquiv C p d).injective
  rw [RingEquiv.apply_symm_apply,iterateFrobeniusEquiv_def,← map_pow]
  change f (iterateFrobeniusEquiv P p d ((iterateFrobeniusEquiv P p d).symm x)) = _
  rw [RingEquiv.apply_symm_apply]

end Lech.RootTower
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_RootTowerNormalizedLength
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open MvPowerSeries
open scoped Classical
open scoped TensorProduct
open IsLocalRing
open MvPowerSeries IsLocalRing
open scoped ENNReal
open scoped ENNReal TensorProduct Classical DirectSum
open TensorProduct
open scoped TensorProduct nonZeroDivisors
open scoped nonZeroDivisors
open scoped BigOperators
open scoped nonZeroDivisors TensorProduct


namespace Lech.RootTower
open Lech.PerfectDomainStages
variable {A B D : Type*} [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
    [CommRing D] [IsDomain D] [Algebra A B] [Algebra A D]
    (p : ℕ) [Fact p.Prime] [CharP A p] [CharP B p] [CharP D p]

lemma perfectAlgEquiv_of (f : B →ₐ[A] D) (hi : Function.Injective f)
    (he : ∃ e : ℕ, ∀ x : D, ∃ b : B, f b = x^(p^e)) (b : B) :
    perfectAlgEquiv p f hi he (PerfectClosure.of B p b) = PerfectClosure.of D p (f b) :=
  perfectMap_of p f.toRingHom b
end Lech.RootTower


open scoped Classical Pointwise
end
end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_TensorRingTwist
attribute [-instance] _root_.OAI.Lech.Koszul.single_linear _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ChangeOfRings

namespace Lech.RootTower
open CategoryTheory
open scoped ENNReal ChangeOfRings
attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm
universe u
variable (σ : Type) (k : Type u) [Fintype σ] [Field k] (p : ℕ) [Fact p.Prime]
  [CharP k p] [PerfectRing k p]
  {D C : Type u} [CommRing D] [CommRing C] [CharP C p] [PerfectRing C p]
  [Algebra (PerfectClosure (MvPowerSeries σ k) p) C]

 

theorem normalizedLength_frobenius_extend (f : D →+* C) (d : ℕ) (M : ModuleCat.{u} D) :
    normalizedLength σ k p
      ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries σ k) p) C)).obj
        ((ModuleCat.extendScalars f).obj M)) =
      ((p : ℝ≥0∞)^(d*Fintype.card σ))⁻¹ * normalizedLength σ k p
        ((ModuleCat.restrictScalars (algebraMap (PerfectClosure (MvPowerSeries σ k) p) C)).obj
          ((ModuleCat.extendScalars
            ((iterateFrobeniusEquiv C p d : C →+* C).comp f)).obj M)) := by
  let P := PerfectClosure (MvPowerSeries σ k) p
  let e := iterateFrobeniusEquiv C p d
  let g := (e : C →+* C).comp f
  have hx : (e.symm : C →+* C).comp g = f := by ext x; exact e.symm_apply_apply (f x)
  let q := Lech.TensorTwist.extendEquiv g e.symm M
  rw [hx] at q
  let E : LinearEquiv (σ' := (iterateFrobeniusEquiv P p d : P →+* P))
      ((iterateFrobeniusEquiv P p d).symm : P →+* P)
      ((ModuleCat.restrictScalars (algebraMap P C)).obj ((ModuleCat.extendScalars g).obj M))
      ((ModuleCat.restrictScalars (algebraMap P C)).obj ((ModuleCat.extendScalars f).obj M)) :=
    { q.toAddEquiv with
      map_smul' := by
        intro a x
        have h := q.map_smulₛₗ (algebraMap P C a)
          (show (ModuleCat.extendScalars g).obj M from x)
        exact h.trans (congrArg (fun c : C => c • q x)
          (map_inverse_frobenius p (algebraMap P C) d a).symm) }
  exact normalizedLength_root_equiv σ k p d E
end Lech.RootTower

end

end OAI
end

section
-- module Solutions.OAIQ032_LECH.Multiplicity_IntermediateTensorLength
attribute [-instance] _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesFiniteColimits _root_.OAI.Lech.PerfectDomainStages.rootStageFunctor_preservesZero _root_.OAI.Lech.extendScalars_additive
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped TensorProduct ENNReal
open CategoryTheory
namespace Lech.FrobeniusIntermediate
open Lech.RootTower Lech.PerfectDomainStages
universe u
variable (σ : Type) (k D : Type u) [Fintype σ] [Field k] [CommRing D] [IsDomain D]
    [Algebra (MvPowerSeries σ k) D]
    (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p] [CharP D p]
    (B : Subalgebra (MvPowerSeries σ k) D)
    (e : ℕ) (he : ∀ x : D, x^(p^e) ∈ B)
local instance instIsDomainMvPowerSeries_solutions_1 : IsDomain (MvPowerSeries σ k) := NoZeroDivisors.to_isDomain _


attribute [local instance] OAI.Lech.FrobeniusIntermediate.instCharPSubtypeMemSubalgebraMvPowerSeries_solutions_1
attribute [local instance] OAI.Lech.FrobeniusIntermediate.instSMulCommClassSubtypeMemSubalgebraMvPowerSeriesPerfectClosure_solutions
theorem normalizedLength_intermediate_tensor_oai (M : ModuleCat.{u} D) :
    normalizedLength σ k p ((PerfectClosure D p) ⊗[D] M) =
      ((p : ℝ≥0∞)^(e*Fintype.card σ))⁻¹ *
        normalizedLength σ k p ((PerfectClosure B p) ⊗[B]
          ((ModuleCat.extendScalars (powerMap p B.toSubring e he)).obj M)) := by
  let P := PerfectClosure (MvPowerSeries σ k) p
  let C := PerfectClosure D p
  let C' := PerfectClosure B p
  let E := perfectAlgEquiv p B.val Subtype.val_injective
    ⟨e,fun d => ⟨⟨d^(p^e),he d⟩,rfl⟩⟩
  let f := (PerfectClosure.of B p).comp (powerMap p B.toSubring e he)
  have hx : E.toRingHom.comp f =
      (iterateFrobeniusEquiv C p e : C →+* C).comp (PerfectClosure.of D p) := by
    ext x
    change E (PerfectClosure.of B p (powerMap p B.toSubring e he x)) =
      iterateFrobeniusEquiv C p e (PerfectClosure.of D p x)
    refine (perfectAlgEquiv_of p B.val Subtype.val_injective
      ⟨e, fun d => ⟨⟨d^(p^e), he d⟩, rfl⟩⟩ (powerMap p B.toSubring e he x)).trans ?_
    rw [iterateFrobeniusEquiv_def,← map_pow]
    rfl
  have hl₁ : normalizedLength σ k p
      ((PerfectClosure B p) ⊗[B] ((ModuleCat.extendScalars (powerMap p B.toSubring e he)).obj M)) =
      normalizedLength σ k p ((ModuleCat.restrictScalars (algebraMap P C')).obj
        ((ModuleCat.extendScalars f).obj M)) := by
    let q := (ModuleCat.extendScalarsComp (powerMap p B.toSubring e he)
      (PerfectClosure.of B p)).app M
    exact ((regularTower σ k p).length_eq_of_equiv
      ((ModuleCat.restrictScalars (algebraMap P C')).mapIso q).toLinearEquiv).symm
  have hl₂ := (regularTower σ k p).length_eq_of_equiv
    (Lech.TensorTwist.algebraExtendEquiv f E M)
  change normalizedLength σ k p _ = normalizedLength σ k p _ at hl₂
  rw [hx] at hl₂
  rw [hl₁,hl₂]
  exact normalizedLength_frobenius_extend σ k p (PerfectClosure.of D p) e M
end Lech.FrobeniusIntermediate

end

end OAI
end

theorem solution.{u} : type_of% @OAI.Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor_oai.{u} := @OAI.Lech.FrobeniusIntermediate.normalizedLength_intermediate_tensor_oai.{u}
