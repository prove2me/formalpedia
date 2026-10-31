-- Prove2me | solution 1 for OAI.NuclearUltrapower.main_statement
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T17:31:11.183265+00:00
-- url     : https://prove2.me/submissions/43768440-8985-40c1-be92-a001ab560c24

import Mathlib
import Definitions.Def_NuclearUltrapower
import Definitions.Def_OAIQ019N044
import Theorems.Thm_OAI_NuclearUltrapower_Elementary_kazhdanSet_generates
import Theorems.Thm_OAI_NuclearUltrapower_SOS_ElementarySpectral_exists_fixed_nearby
import Theorems.Thm_OAI_NuclearUltrapower_fullGroup_no_nuclear_ultrapower

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FiniteRepresentations
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UltraPreHilbert.instAddCommGroupSubtypePreLpMemAddSubgroup _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
universe u v w
open scoped TensorProduct Topology
open Filter
noncomputable section
open scoped InnerProductSpace

namespace NuclearUltrapower

attribute [instance] FiniteUnitaryRep.normed FiniteUnitaryRep.inner
  FiniteUnitaryRep.complete FiniteUnitaryRep.finite FiniteUnitaryRep.nontrivial

variable {Γ : Type u} [Group Γ]

namespace FiniteUnitaryRep

theorem restrict_embeds (π : FiniteUnitaryRep.{u,v} Γ) (W : Submodule ℂ π)
    (hW : ∀ g x, x ∈ W → π.action g x ∈ W) [Nontrivial W] :
    (π.restrict W hW).Embeds π :=
  ⟨W.subtypeₗᵢ, fun _ _ => rfl⟩

/-- Every nonzero finite-dimensional unitary representation has an irreducible
subrepresentation. This uses minimal dimension, not a semisimplicity assumption. -/
theorem exists_irreducible (π : FiniteUnitaryRep.{u,v} Γ) :
    ∃ τ : FiniteUnitaryRep.{u,v} Γ, τ.Irreducible ∧ τ.Embeds π := by
  let P (n : ℕ) := ∃ W : Submodule ℂ π, W ≠ ⊥ ∧
    (∀ g x, x ∈ W → π.action g x ∈ W) ∧ Module.finrank ℂ W = n
  have hP : ∃ n, P n := ⟨Module.finrank ℂ (⊤ : Submodule ℂ π),
    ⊤, top_ne_bot, fun _ _ _ => Submodule.mem_top, rfl⟩
  classical
  obtain ⟨W, hW0, hW, hdim⟩ := Nat.find_spec hP
  let : Nontrivial W := Submodule.nontrivial_iff_ne_bot.mpr hW0
  refine ⟨π.restrict W hW, ?_, π.restrict_embeds W hW⟩
  intro V hV
  change Submodule ℂ W at V
  by_cases hV0 : V = ⊥
  · exact Or.inl hV0
  right
  let U : Submodule ℂ π := V.map W.subtype
  have hU0 : U ≠ ⊥ := by
    intro hU
    apply hV0
    apply le_antisymm ?_ bot_le
    intro x hx
    have hmem : (x : π) ∈ U := ⟨x, hx, rfl⟩
    rw [hU] at hmem
    exact W.subtype_injective hmem
  have hU (g : Γ) (x : π) (hx : x ∈ U) : π.action g x ∈ U := by
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨(π.restrict W hW).action g y, hV g y hy, rfl⟩
  have heq : Module.finrank ℂ U = Module.finrank ℂ V :=
    LinearEquiv.finrank_eq (V.equivMapOfInjective W.subtype W.subtype_injective).symm
  have hmin : Nat.find hP ≤ Module.finrank ℂ V := by
    rw [← heq]
    exact Nat.find_min' hP ⟨U, hU0, hU, rfl⟩
  have he : Module.finrank ℂ V = Module.finrank ℂ (π.restrict W hW) := by
    apply le_antisymm (Submodule.finrank_le V)
    exact hdim ▸ hmin
  exact Submodule.eq_top_of_finrank_eq he

end FiniteUnitaryRep
end NuclearUltrapower

end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_FullGroupAlgebra
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAlgebraComplexAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instStarAlgebra _root_.OAI.NuclearUltrapower.instStarNormUltrapower _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped MonoidAlgebra

noncomputable section
open UniformSpace

namespace NuclearUltrapower.FullGroupModel
open UniformSpace
open scoped MonoidAlgebra CStarAlgebra
open GroupStarAlgebra
variable (Γ : Type) [Group Γ]

/-- The linear span, not just the algebra generated by the generators, is dense. -/
theorem dense_span : Dense (Submodule.span ℂ (Set.range (fun g => (inclusion Γ g : Full Γ))) : Set (Full Γ)) := by
  apply Completion.denseRange_coe.mono
  rintro _ ⟨x, rfl⟩
  have hin (y : ℂ[Γ]) : algebraicInclusion Γ y ∈
      Submodule.span ℂ (Set.range (fun g => (inclusion Γ g : Full Γ))) := by
    induction y using MonoidAlgebra.induction_on with
    | of g => exact Submodule.subset_span ⟨g, rfl⟩
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
    | smul c x hx => simpa only [map_smul] using Submodule.smul_mem _ c hx
  exact hin x

/-- Uniqueness is proved from continuity and dense generation. -/
theorem modelMap_unique {D : Type} [CStarAlgebra D] (ρ : Γ →* unitary D)
    (φ : Full Γ →⋆ₐ[ℂ] D) (hφ : ∀ g, φ (inclusion Γ g) = (ρ g : D)) :
    φ = modelMap Γ ρ := by
  have he (x : ℂ[Γ]) : φ (algebraicInclusion Γ x) = modelMap Γ ρ (algebraicInclusion Γ x) := by
    induction x using MonoidAlgebra.induction_on with
    | of g => exact (hφ g).trans (modelMap_generator Γ ρ g).symm
    | add x y hx hy => simp only [map_add, hx, hy]
    | smul c x hx => simp only [map_smul, hx]
  have hc : Continuous (φ : Full Γ → D) :=
    AddMonoidHomClass.continuous_of_bound φ 1 (by
      intro x
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le φ x)
  have hd : Continuous (modelMap Γ ρ : Full Γ → D) :=
    AddMonoidHomClass.continuous_of_bound (modelMap Γ ρ) 1 (by
      intro x
      simpa only [one_mul] using NonUnitalStarAlgHom.norm_apply_le (modelMap Γ ρ) x)
  apply DFunLike.ext'
  exact Completion.denseRange_coe.equalizer hc hd (funext he)

/-- Countability of the group gives the standing separability conclusion. -/
instance instSeparableSpaceFullOfCountable [Countable Γ] : TopologicalSpace.SeparableSpace (Full Γ) := by
  have hs : TopologicalSpace.IsSeparable (Set.range (fun g => (inclusion Γ g : Full Γ))) :=
    (Set.countable_range _).isSeparable
  have ht := hs.span (R := ℂ)
  have hc := ht.closure
  rw [(dense_span Γ).closure_eq] at hc
  exact TopologicalSpace.isSeparable_univ_iff.mp hc

end NuclearUltrapower.FullGroupModel
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_SOSGap
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.strongDualInner
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.SOSEnergy
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H]

theorem energy_nonneg (S : Finset Γ) (ρ : Γ →* (H ≃ₗᵢ[ℂ] H)) (x : H) :
    0 ≤ energy S ρ x := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

end NuclearUltrapower.SOSEnergy

end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Kazhdan
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing _root_.OAI.NuclearUltrapower.VariableUltra.instCStarAlgebraAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNontrivialAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedAddCommGroupAlgebra _root_.OAI.NuclearUltrapower.VariableUltra.instNormedRingAlgebra _root_.OAI.NuclearUltrapower.induced_nontrivial _root_.OAI.NuclearUltrapower.instCountableDyadic _root_.OAI.NuclearUltrapower.instCountableG _root_.OAI.NuclearUltrapower.instCountableSL3Z _root_.OAI.NuclearUltrapower.instCountableVector3 _root_.OAI.NuclearUltrapower.lp_finiteDimensional _root_.OAI.NuclearUltrapower.tensorHilbertNontrivial
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary

theorem integralTheta_injective : Function.Injective integralTheta := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have hi := congrArg (fun x : IntegralGroup => x.left.toAdd i) he
    change 2 * g.left.toAdd i = 2 * h.left.toAdd i at hi
    omega
  · simpa only [integralTheta_right] using congrArg (fun x : IntegralGroup => x.right) he

/-- The source group law implements exactly multiplication of translations by two. -/
theorem stableLetter_conjugation (g : IntegralGroup) :
    stableLetter * integralInclusion g * stableLetter⁻¹ = integralInclusion (integralTheta g) := by
  apply (mul_inv_eq_iff_eq_mul).mpr
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    change 0 + ((dilationAction (1, Multiplicative.ofAdd (1 : ℤ)))
      (fun j => (g.left.toAdd j : Dyadic))) i =
      ((2 * g.left.toAdd i : ℤ) : Dyadic) +
      (dilationAction (g.right, 1) (0 : Vector3)) i
    simp [dilationAction, matrixAction, LinearEquiv.smulOfUnit, Units.smul_def]
  · change (1, Multiplicative.ofAdd (1 : ℤ)) * ((g.right : SL3Z), 1) =
      ((g.right : SL3Z), 1) * (1, Multiplicative.ofAdd (1 : ℤ))
    simp

/-- The integral copy is genuinely a subgroup, not merely a homomorphic image. -/
theorem integralInclusion_injective : Function.Injective integralInclusion := by
  intro g h he
  apply SemidirectProduct.ext
  · apply Multiplicative.toAdd.injective
    funext i
    have hi := congrArg (fun x : G => x.left.toAdd i) he
    change (g.left.toAdd i : Dyadic) = (h.left.toAdd i : Dyadic) at hi
    apply IsLocalization.injective (S := Dyadic)
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero (by norm_num : (2 : ℤ) ≠ 0)))
    simpa only [eq_intCast] using hi
  · exact Subtype.ext (congrArg (fun x : G => x.right.1) he)

theorem integralTheta_index : integralTheta.range.index = 8 := by
  rw [Subgroup.index_eq_card, Nat.card_congr thetaCosetEquiv]
  simp [Residue3, Nat.card_eq_fintype_card]

instance instFiniteIndexIntegralGroupRangeIntegralTheta : integralTheta.range.FiniteIndex := ⟨by rw [integralTheta_index]; norm_num⟩

/-- A translation-fixed vector in the augmentation representation is zero. -/
theorem augmentation_no_translation_invariants (f : augmentationRep)
    (hf : ∀ v : IntegralVector3, augmentationRep.action (integralTranslation v) f = f) :
    f = 0 := by
  have ht (v : IntegralVector3) (x : Residue3) :
      f.val (residuePermutation (integralTranslation v) x) = f.val x := by
    have he := congrArg (fun z : augmentationRep => z.val (residuePermutation (integralTranslation v) x)) (hf v)
    change f.val ((residuePermutation (integralTranslation v)).symm
      (residuePermutation (integralTranslation v) x)) = _ at he
    simpa only [Equiv.symm_apply_apply] using he.symm
  have hc (x : Residue3) : f.val x = f.val 0 := by
    have he : residuePermutation (integralTranslation (fun i => (x i).val)) 0 = x := by
      ext i
      simp [residue, integralTranslation, residueMatrix]
    simpa only [he] using ht (fun i => (x i).val) 0
  have hz : f.val 0 = 0 := by
    have hs := f.property
    rw [mem_augmentation] at hs
    simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hs
    have hn : (Fintype.card Residue3 : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    exact (mul_eq_zero.mp hs).resolve_left hn
  apply Subtype.ext
  ext x
  exact (hc x).trans hz

/-- All positive dilation pullbacks kill the translation subgroup. -/
theorem augmentation_pull_translation (j : ℕ) (hj : 0 < j) (v : IntegralVector3) :
    augmentationRep.action ((integralTheta ^ j) (integralTranslation v)) = 1 := by
  have hr : residuePermutation ((integralTheta ^ j) (integralTranslation v)) = 1 := by
    rw [integralTheta_pow_translation]
    ext x i
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    simp [residue, integralTranslation, residueMatrix, htwo, Nat.ne_of_gt hj]
  ext f
  apply Subtype.ext
  change LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ
    (residuePermutation ((integralTheta ^ j) (integralTranslation v))) f.val = f.val
  rw [hr]
  rfl

/-- The required irreducible mod-two representation is a constituent of the
augmentation representation, hence has no translation-fixed vectors. -/
theorem exists_aperiodic_integral_rep :
    ∃ π : FiniteUnitaryRep.{0,0} IntegralGroup, π.Irreducible ∧
      (∀ j : ℕ, 0 < j → ¬ π.Equivalent (π.pull (integralTheta ^ j))) := by
  obtain ⟨π, hπ, T, hT⟩ := FiniteUnitaryRep.exists_irreducible augmentationRep
  refine ⟨π, hπ, fun j hj he => ?_⟩
  obtain ⟨U, hU⟩ := he
  have hkill (v : IntegralVector3) (x : π) :
      π.action ((integralTheta ^ j) (integralTranslation v)) x = x := by
    apply T.injective
    rw [hT, augmentation_pull_translation j hj]
    rfl
  have hfix (x : π) (v : IntegralVector3) : π.action (integralTranslation v) x = x := by
    apply U.injective
    rw [hU]
    change π.action ((integralTheta ^ j) (integralTranslation v)) (U x) = U x
    exact hkill v (U x)
  have hall (x : π) : x = 0 := by
    apply T.injective
    rw [map_zero]
    apply augmentation_no_translation_invariants
    intro v
    rw [← hT, hfix]
  obtain ⟨x, hx⟩ := exists_ne (0 : π)
  exact hx (hall x)

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Elementary
open SOS

theorem transvection_basis {i j : Fin 3} (h : i ≠ j) (k : ℤ) :
    Matrix.SpecialLinearGroup.toLin' (elementaryTransvection h k) (basisVector j) =
      basisVector j + k • basisVector i := by
  exact Matrix.SpecialLinearGroup.transvection_smul_single_snd h k

theorem conjugate_translation (M : SOS.E) (v : IntegralVector3) :
    linearInclusion M * integralTranslation v * (linearInclusion M)⁻¹ =
      integralTranslation (Matrix.SpecialLinearGroup.toLin' (M : SL3Z) v) := by
  change SemidirectProduct.inr M * SemidirectProduct.inl (Multiplicative.ofAdd v) *
    (SemidirectProduct.inr M)⁻¹ = SemidirectProduct.inl
      ((integralAction M) (Multiplicative.ofAdd v))
  rw [← map_inv]
  exact (SemidirectProduct.inl_aut M (Multiplicative.ofAdd v)).symm

theorem translation_add (v w : IntegralVector3) :
    integralTranslation (v+w) = integralTranslation v * integralTranslation w := by
  exact map_mul SemidirectProduct.inl (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)

theorem translation_neg (v : IntegralVector3) :
    integralTranslation (-v) = (integralTranslation v)⁻¹ := by
  exact map_inv SemidirectProduct.inl (Multiplicative.ofAdd v)

theorem translation_sub (v w : IntegralVector3) :
    integralTranslation (v-w) = integralTranslation v * (integralTranslation w)⁻¹ := by
  rw [sub_eq_add_neg, translation_add, translation_neg]

theorem translation_three (v : IntegralVector3) :
    integralTranslation v = integralTranslation (v 0 • basisVector 0) *
      integralTranslation (v 1 • basisVector 1) * integralTranslation (v 2 • basisVector 2) := by
  have hv : v = v 0 • basisVector 0 + v 1 • basisVector 1 + v 2 • basisVector 2 := by
    ext j
    fin_cases j <;> simp [basisVector]
  calc
    _ = integralTranslation (v 0 • basisVector 0 + v 1 • basisVector 1 + v 2 • basisVector 2) := congrArg _ hv
    _ = _ := by rw [translation_add, translation_add]

theorem normal_form (g : IntegralGroup) :
    g = integralTranslation g.left.toAdd * linearInclusion g.right := by
  exact (SemidirectProduct.inl_left_mul_inr_right g).symm

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Displacement
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))

theorem mul_le (g h : Γ) (x : H) :
    dist ρ (g*h) x ≤ dist ρ g x + dist ρ h x := by
  have he : ρ (g*h) x - x = (ρ g x-x) + ρ g (ρ h x-x) := by
    rw [map_mul]
    change ρ g (ρ h x)-x = _
    rw [map_sub]
    abel
  unfold dist
  rw [he]
  exact (norm_add_le _ _).trans_eq (by rw [(ρ g).norm_map])

theorem conjugate (g h : Γ) (x : H) (hg : ρ g x = x) :
    dist ρ (g*h*g⁻¹) x = dist ρ h x := by
  have hi : ρ g⁻¹ x = x := by
    apply (ρ g).injective
    change (ρ g * ρ g⁻¹) x = ρ g x
    rw [← map_mul, mul_inv_cancel, map_one]
    exact hg.symm
  unfold dist
  simp only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply, hi]
  calc
    _ = ‖ρ g (ρ h x-x)‖ := by rw [map_sub, hg]
    _ = _ := (ρ g).norm_map _

theorem change_vector (g : Γ) (x y : H) :
    dist ρ g y ≤ 2 * ‖x-y‖ + dist ρ g x := by
  have he : ρ g y-y = -ρ g (x-y) + (ρ g x-x) + (x-y) := by
    rw [map_sub]
    abel
  unfold dist
  rw [he]
  calc
    _ ≤ ‖-ρ g (x-y)‖ + ‖ρ g x-x‖ + ‖x-y‖ := norm_add₃_le
    _ = _ := by rw [norm_neg, (ρ g).norm_map]; ring

end NuclearUltrapower.Displacement
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower
variable {Γ H : Type*} [Group Γ] [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The closest point to zero in a closed convex unitary orbit hull is fixed.
This supplies the bounded-orbit implication without using property T as an axiom. -/
theorem unitary_orbit_norm_le (ρ : Γ →* (H ≃ₗᵢ[ℂ] H))
    (hno : ∀ y : H, (∀ g, ρ g y = y) → y = 0)
    (x : H) (r : ℝ) (hbound : ∀ g, ‖ρ g x - x‖ ≤ r) : ‖x‖ ≤ r := by
  let : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  let K : Set H := closure (convexHull ℝ (Set.range (fun g => ρ g x)))
  have hclosed : IsClosed K := isClosed_closure
  have hconvex : Convex ℝ K := (convex_convexHull ℝ _).closure
  have horbit (g : Γ) : ρ g x ∈ K := subset_closure (subset_convexHull ℝ _ (Set.mem_range_self g))
  have hnonempty : K.Nonempty := ⟨ρ 1 x, horbit 1⟩
  have hinvariant (g : Γ) : ∀ y ∈ K, ρ g y ∈ K := by
    have hpre : Convex ℝ ((ρ g) ⁻¹' K) :=
      hconvex.linear_preimage ((ρ g).toLinearMap.restrictScalars ℝ)
    apply closure_minimal (convexHull_min ?_ hpre) (hclosed.preimage (ρ g).continuous)
    rintro _ ⟨h, rfl⟩
    change ρ g (ρ h x) ∈ K
    simpa only [map_mul, LinearIsometryEquiv.coe_mul, Function.comp_apply] using horbit (g*h)
  obtain ⟨z, hz, hmin⟩ := exists_norm_eq_iInf_of_complete_convex hnonempty
    hclosed.isComplete hconvex (0 : H)
  have hfix (g : Γ) : ρ g z = z := by
    have hi := (norm_eq_iInf_iff_real_inner_le_zero hconvex hz).mp hmin
      (ρ g z) (hinvariant g z hz)
    have hn := norm_sub_sq (𝕜 := ℝ) (ρ g z) z
    rw [(ρ g).norm_map, real_inner_comm] at hn
    simp only [zero_sub, inner_neg_left, inner_sub_right, real_inner_self_eq_norm_sq] at hi
    simp only [RCLike.re_to_real] at hn
    have hm : ‖ρ g z - z‖ = 0 := by nlinarith [norm_nonneg (ρ g z-z)]
    exact sub_eq_zero.mp (norm_eq_zero.mp hm)
  have hz0 := hno z hfix
  have hb : K ⊆ Metric.closedBall x r := by
    apply closure_minimal (convexHull_min ?_ (convex_closedBall x r)) Metric.isClosed_closedBall
    rintro _ ⟨g, rfl⟩
    simpa only [Metric.mem_closedBall, dist_eq_norm] using hbound g
  have := hb hz
  simpa [hz0, Metric.mem_closedBall, dist_eq_norm] using this
end NuclearUltrapower
end
end

section

noncomputable section
open scoped InnerProductSpace
namespace NuclearUltrapower.Elementary
open SOS SOSEnergy
open Displacement (dist)

theorem kazhdanSet_nonempty : kazhdanSet.Nonempty := by
  classical
  refine ⟨integralTranslation (basisVector 0), ?_⟩
  exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨0,Finset.mem_univ _,rfl⟩)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
theorem translation_line_displacement (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (y : H) (C : ℝ) (hfix : ∀ M : E, ρ (linearInclusion M) y = y)
    (hs : ∀ i : Fin 3, dist ρ (integralTranslation (basisVector i)) y ≤ C)
    (i : Fin 3) (k : ℤ) : dist ρ (integralTranslation (k • basisVector i)) y ≤ 2*C := by
  obtain ⟨j,hj⟩ : ∃ j : Fin 3, i ≠ j := by
    by_cases hi : i = 0
    · exact ⟨1,by simp [hi]⟩
    · exact ⟨0,hi⟩
  let M := elementaryTransvection hj k
  have hv : k • basisVector i =
      Matrix.SpecialLinearGroup.toLin' (M : SL3Z) (basisVector j) - basisVector j := by
    rw [transvection_basis]
    abel
  rw [hv, translation_sub, ← conjugate_translation]
  have hm : ρ (linearInclusion M) y = y := hfix M
  exact (Displacement.mul_le ρ _ _ y).trans (by
    rw [Displacement.conjugate ρ _ _ _ hm, Displacement.inv]
    linarith [hs j])

omit [CompleteSpace H] in
theorem translation_displacement (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (y : H) (C : ℝ) (hfix : ∀ M : E, ρ (linearInclusion M) y = y)
    (hs : ∀ i : Fin 3, dist ρ (integralTranslation (basisVector i)) y ≤ C)
    (v : IntegralVector3) : dist ρ (integralTranslation v) y ≤ 6*C := by
  have h0 := translation_line_displacement ρ y C hfix hs 0 (v 0)
  have h1 := translation_line_displacement ρ y C hfix hs 1 (v 1)
  have h2 := translation_line_displacement ρ y C hfix hs 2 (v 2)
  let a := integralTranslation (v 0 • basisVector 0)
  let b := integralTranslation (v 1 • basisVector 1)
  let c := integralTranslation (v 2 • basisVector 2)
  have ht := Displacement.mul_le ρ (a*b) c y
  have ht' := Displacement.mul_le ρ a b y
  rw [translation_three]
  change dist ρ ((a*b)*c) y ≤ _
  linarith

omit [CompleteSpace H] in
theorem integral_displacement (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (y : H) (C : ℝ) (hfix : ∀ M : E, ρ (linearInclusion M) y = y)
    (hs : ∀ i : Fin 3, dist ρ (integralTranslation (basisVector i)) y ≤ C)
    (g : IntegralGroup) : dist ρ g y ≤ 6*C := by
  conv_lhs => rw [normal_form g]
  have hm : dist ρ (linearInclusion g.right) y = 0 := by
    simp only [Displacement.dist, hfix g.right, sub_self, norm_zero]
  exact (Displacement.mul_le ρ _ _ y).trans (by
    rw [hm,add_zero]
    exact translation_displacement ρ y C hfix hs g.left.toAdd)

/-- This is the needed absolute gap, proved from the certified elementary gap
and the elementary conjugacy identities on integral translations. -/
theorem kazhdan_energy (ρ : IntegralGroup →* (H ≃ₗᵢ[ℂ] H))
    (hno : ∀ y : H, (∀ g, ρ g y = y) → y = 0) (x : H) :
    (1/4000 : ℝ) * ‖x‖ ^ 2 ≤ energy kazhdanSet ρ x := by
  classical
  let T := energy kazhdanSet ρ x
  let r := Real.sqrt T
  have hT : 0 ≤ T := energy_nonneg _ _ _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r^2 = T := Real.sq_sqrt hT
  have he : energy eGenSet (ρ.comp linearInclusion) x ≤ T := by
    change (∑ s ∈ eGenSet, ‖ρ (linearInclusion s) x-x‖^2) ≤
      ∑ s ∈ kazhdanSet, ‖ρ s x-x‖^2
    have hh : (∑ s ∈ eGenSet.image linearInclusion, ‖ρ s x-x‖^2) =
        ∑ s ∈ eGenSet, ‖ρ (linearInclusion s) x-x‖^2 := by
      apply Finset.sum_image
      intro a _ b _ hab
      exact congrArg SemidirectProduct.right hab
    rw [← hh]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left)
      (fun _ _ _ => sq_nonneg _)
  obtain ⟨y,hfix,hy⟩ := SOS.ElementarySpectral.exists_fixed_nearby (ρ.comp linearInclusion) x
  have hxy : ‖x-y‖ ≤ 4*r := by
    nlinarith [hy.trans he, norm_nonneg (x-y)]
  have hs (i : Fin 3) : dist ρ (integralTranslation (basisVector i)) x ≤ r := by
    apply (Real.le_sqrt (norm_nonneg _) hT).mpr
    change ‖ρ (integralTranslation (basisVector i)) x-x‖^2 ≤
      ∑ s ∈ kazhdanSet, ‖ρ s x-x‖^2
    exact Finset.single_le_sum (f := fun s : IntegralGroup => ‖ρ s x-x‖^2) (fun _ _ => sq_nonneg _)
      (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩))
  have hsy (i : Fin 3) : dist ρ (integralTranslation (basisVector i)) y ≤ 9*r := by
    have h := Displacement.change_vector ρ (integralTranslation (basisVector i)) x y
    linarith [hs i]
  have hall : ∀ g : IntegralGroup, dist ρ g y ≤ 54*r := by
    intro g
    convert integral_displacement ρ y (9*r) hfix hsy g using 1
    all_goals try with_reducible_and_instances rfl
    ring
  have hyn : ‖y‖ ≤ 54*r := unitary_orbit_norm_le ρ hno y (54*r) hall
  have hxn : ‖x‖ ≤ 58*r := by
    have h := norm_add_le (x-y) y
    rw [sub_add_cancel] at h
    linarith
  change (1/4000 : ℝ) * ‖x‖^2 ≤ T
  nlinarith [sq_nonneg (58*r-‖x‖), norm_nonneg x]

end NuclearUltrapower.Elementary
end
end

section

noncomputable section
namespace NuclearUltrapower.Elementary
universe v

theorem hasKazhdanGap : HasKazhdanGap.{0,v} kazhdanSet (1/4000) := by
  intro H _ _ _ ρ hρ x
  exact kazhdan_energy ρ hρ x

end NuclearUltrapower.Elementary
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_Obstruction
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instSeminormedRingPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarPoly _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.CuntzWords.instFintypeWord
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace NuclearUltrapower

/-- The exact dyadic ambient group has a full group C*-algebra with the stated
universal property, separability, and obstruction for every nuclear target. -/
theorem main_statement_oai : MainStatement.{0} := by
  let A : UnitalCStar := ⟨FullGroupModel.Full G⟩
  refine ⟨A, FullGroupModel.inclusion G, ?_, inferInstance, ?_⟩
  · refine ⟨FullGroupModel.dense_span G, ?_⟩
    intro D ρ
    refine ⟨FullGroupModel.modelMap G ρ, FullGroupModel.modelMap_generator G ρ, ?_⟩
    intro φ hφ
    exact FullGroupModel.modelMap_unique G ρ φ hφ
  · intro B hB ω hω
    obtain ⟨π,hπ,haπ⟩ := Elementary.exists_aperiodic_integral_rep
    apply fullGroup_no_nuclear_ultrapower Elementary.integralInclusion
      Elementary.integralInclusion_injective Elementary.integralTheta
      Elementary.integralTheta_injective Elementary.stableLetter ?_
      Elementary.kazhdanSet Elementary.kazhdanSet_nonempty Elementary.kazhdanSet_generates
      (1/4000) (by norm_num) ?_ Elementary.hasKazhdanGap π hπ haπ hB ω hω
    · intro g
      have h := Elementary.stableLetter_conjugation g
      calc
        _ = (Elementary.stableLetter * Elementary.integralInclusion g *
          Elementary.stableLetter⁻¹) * Elementary.stableLetter := congrArg (· * _) h.symm
        _ = _ := by group
    · have hc : 1 ≤ (Elementary.kazhdanSet.card : ℝ) := by
        exact_mod_cast Finset.card_pos.mpr Elementary.kazhdanSet_nonempty
      linarith

end NuclearUltrapower
end
end

end OAI
end

theorem solution : type_of% @OAI.NuclearUltrapower.main_statement_oai := @OAI.NuclearUltrapower.main_statement_oai
