-- Prove2me | solution 1 for OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T15:44:41.207847+00:00
-- url     : https://prove2.me/submissions/28a3fc0b-23b0-4015-9899-22415894870b

import Mathlib
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Finiteness.Defs
import Definitions.Def_FinitisticAsymmetry
import Definitions.Def_Q221FA002

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_Telescopes
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ n, K n ⟶ K (n+1))

lemma moduleTelescope_at_zero (j : ℤ) (x : Π₀ n, (K n).X j) :
    (moduleTelescopeLinear K f j x) 0 = x 0 := by
  classical
  let : DecidableEq ℕ := Classical.typeDecidableEq ℕ
  have h : (DFinsupp.lapply 0).comp (moduleTelescopeLinear K f j) =
      (DFinsupp.lapply 0 : (Π₀ n, (K n).X j) →ₗ[R] (K 0).X j) := by
    apply DFinsupp.lhom_ext
    intro n y
    have hlin := congrArg (fun t => (t.f j).hom) (telescopeMap_inj f _ (moduleSumComplexIsColimit K) n)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, ModuleCat.hom_sub, ModuleCat.hom_comp] at hlin
    have hfun := LinearMap.congr_fun hlin y
    simp only [moduleSumComplexCofan, cofan_mk_inj, moduleSumComplexInj] at hfun
    have hsing : moduleTelescopeLinear K f j (DFinsupp.single n y) =
        (DFinsupp.single n y : Π₀ n, (K n).X j) - DFinsupp.single (n+1) ((f n).f j y) := by
      simpa [moduleTelescopeLinear, moduleTelescopeMap, moduleSumComplexCofan, moduleSumComplexInj, moduleSumComplex] using! hfun
    change (moduleTelescopeLinear K f j (DFinsupp.single n y)) 0 = _
    rw [hsing, DFinsupp.sub_apply]
    simp [DFinsupp.lapply_apply]
  exact LinearMap.congr_fun h x

lemma moduleTelescope_at_succ (j : ℤ) (x : Π₀ n, (K n).X j) (n : ℕ) :
    (moduleTelescopeLinear K f j x) (n+1) = x (n+1) - (f n).f j (x n) := by
  classical
  let : DecidableEq ℕ := Classical.typeDecidableEq ℕ
  have h : (DFinsupp.lapply (n+1)).comp (moduleTelescopeLinear K f j) =
      (DFinsupp.lapply (n+1) : (Π₀ n, (K n).X j) →ₗ[R] (K (n+1)).X j) -
        ((f n).f j).hom.comp (DFinsupp.lapply n) := by
    apply DFinsupp.lhom_ext
    intro m y
    have hlin := congrArg (fun t => (t.f j).hom) (telescopeMap_inj f _ (moduleSumComplexIsColimit K) m)
    simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply, ModuleCat.hom_sub, ModuleCat.hom_comp] at hlin
    have hfun := LinearMap.congr_fun hlin y
    simp only [moduleSumComplexCofan, cofan_mk_inj, moduleSumComplexInj] at hfun
    have hsing : moduleTelescopeLinear K f j (DFinsupp.single m y) =
        (DFinsupp.single m y : Π₀ n, (K n).X j) - DFinsupp.single (m+1) ((f m).f j y) := by
      simpa [moduleTelescopeLinear, moduleTelescopeMap, moduleSumComplexCofan, moduleSumComplexInj, moduleSumComplex] using! hfun
    change (moduleTelescopeLinear K f j (DFinsupp.single m y)) (n+1) = _
    rw [hsing, DFinsupp.sub_apply]
    by_cases hmn : m = n
    · subst m
      simp
    · simp [hmn]
  exact LinearMap.congr_fun h x

instance moduleTelescopeMap_mono : Mono (moduleTelescopeMap K f) := by
  apply HomologicalComplex.mono_of_mono_f
  intro j
  rw [ModuleCat.mono_iff_injective]
  apply (injective_iff_map_eq_zero _).2
  change ∀ (x : Π₀ n, (K n).X j), moduleTelescopeLinear K f j x = 0 → x = 0
  intro x hx
  have he (n : ℕ) : x n = 0 := by
    induction n with
    | zero => simpa [hx] using (moduleTelescope_at_zero K f j x).symm
    | succ n ih =>
      have h := moduleTelescope_at_succ K f j x n
      rw [hx, ih, map_zero, sub_zero] at h
      exact h.symm
  exact DFinsupp.ext he

end

universe u w
variable {R : Type u} [Ring R]
variable (K : ℕ → CochainComplex (ModuleCat.{u} R) ℤ) (f : ∀ n, K n ⟶ K (n+1))
variable (c : Cocone (Functor.ofSequence f)) (hc : IsColimit c)

lemma moduleTelescope_shortExact (hc : IsColimit c) : (moduleTelescopeShortComplex K f c).ShortExact where
  mono_f := by change Mono (moduleTelescopeMap K f); infer_instance
  epi_g := epi_of_isColimit_cofork (telescopeCokernel f _ (moduleSumComplexIsColimit K) c hc)
  exact := (moduleTelescopeShortComplex K f c).exact_of_g_is_cokernel
    (telescopeCokernel f _ (moduleSumComplexIsColimit K) c hc)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

lemma localizing_sequence_colimit (hc : IsColimit c) (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]
    (hK : ∀ n, P (DerivedCategory.Q.obj (K n))) : P (DerivedCategory.Q.obj c.pt) := by
  have hs : P (DerivedCategory.Q.obj (moduleSumComplex K)) :=
    P.prop_of_isColimit (derivedCofanIsColimit _ (moduleSumComplexIsColimit K))
      (fun n => hK n.as)
  exact P.ext_of_isTriangulatedClosed₃ _
    (DerivedCategory.triangleOfSES_distinguished (moduleTelescope_shortExact K f c hc)) hs hs

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_Truncations
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u
variable {R : Type u} [Ring R]

lemma cut_shortExact (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ) :
    (cutShortComplex K a).ShortExact where
  exact := by
    apply HomologicalComplex.exact_of_degreewise_exact
    intro j
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    change ↥(cutSub K a j) at x
    change (cutπ K a).f j x = 0 at hx
    by_cases h : j = a
    · subst j
      have hi : Function.Injective ((cutπ K a).f a) :=
        (ModuleCat.mono_iff_injective _).1 inferInstance
      have hx' : x = 0 := hi (hx.trans (map_zero _).symm)
      exact ⟨0, by rw [hx']; rfl⟩
    · refine ⟨⟨(x : K.X j), ?_⟩, ?_⟩
      · have hx' := x.property
        rw [mem_cutSub] at hx' ⊢
        exact hx'.imp (fun h' => by omega) id
      · rfl
  mono_f := by change Mono (cutMap K (show a ≤ a+1 by omega)); infer_instance
  epi_g := by change Epi (cutπ K a); infer_instance

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_BoundedGeneration
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.columnFunctor_additive _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u w
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ) (b : ℤ)
  (hK : ∀ j, b < j → IsZero (K.X j))

include hK in
lemma cut_isZero_of_upperBound (a : ℤ) (ha : b < a) : IsZero (cut K a) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext j
  have hz : IsZero ((cut K a).X j) := by
    by_cases h : a ≤ j
    · have := cutι_f_isIso K a j h
      exact (hK j (lt_of_lt_of_le ha h)).of_iso (asIso ((cutι K a).f j))
    · exact cut_isZero_X K a j (by omega)
  exact hz.eq_of_src _ _

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]

include b hK in
lemma prop_cut_of_terms (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
    [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
    (hterms : ∀ j, P (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) j).obj (K.X j))))
    (a : ℤ) : P (DerivedCategory.Q.obj (cut K a)) := by
  have step (a : ℤ) (ha : P (DerivedCategory.Q.obj (cut K (a+1)))) :
      P (DerivedCategory.Q.obj (cut K a)) :=
    P.ext_of_isTriangulatedClosed₂ _
      (DerivedCategory.triangleOfSES_distinguished (cut_shortExact K a)) ha (hterms a)
  have h (n : ℕ) : P (DerivedCategory.Q.obj (cut K (b+1-(n : ℤ)))) := by
    induction n with
    | zero =>
      exact P.prop_of_isZero (DerivedCategory.Q.map_isZero
        (cut_isZero_of_upperBound K b hK _ (by omega)))
    | succ n ih =>
      apply step
      convert ih using 1
      all_goals try with_reducible_and_instances rfl
      congr 2
      omega
  by_cases ha : a ≤ b+1
  · have he : b+1-((b+1-a).toNat : ℤ) = a := by omega
    simpa only [he] using h ((b+1-a).toNat)
  · exact P.prop_of_isZero (DerivedCategory.Q.map_isZero
      (cut_isZero_of_upperBound K b hK a (by omega)))

end

universe u w
variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

omit [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_of_zero (M : ModuleCat R)
    (hM : P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)) (j : ℤ) :
    P (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat R) (ComplexShape.up ℤ) j).obj M)) := by
  apply P.prop_of_iso ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) j).app M)
  apply P.prop_of_iso (((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (-j) j 0 (by omega)).app M)
  exact P.le_shift (-j) _ hM

lemma prop_of_boundedAbove_terms (K : CochainComplex (ModuleCat R) ℤ)
    (b : ℤ) (hb : ∀ j, b < j → IsZero (K.X j))
    (hterms : ∀ j, P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj (K.X j))) :
    P (DerivedCategory.Q.obj K) := by
  exact localizing_sequence_colimit (fun n => cut K (-(n : ℤ))) (cutSequenceMap K)
    (cutSequenceCocone K) (cutSequenceIsColimit K) P
    (fun n => prop_cut_of_terms K b hb P (fun j => prop_single_of_zero P _ (hterms j) j) _)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_ExactExtension
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u v t t'
variable {C : Type u} [Category.{v} C] [Abelian C]
variable {ι : Type t} {ι' : Type t'} {c : ComplexShape ι} {c' : ComplexShape ι'}
variable (e : c.Embedding c') (S : ShortComplex (HomologicalComplex C c))

lemma extend_shortExact (hS : S.ShortExact) : (S.map (e.extendFunctor C)).ShortExact := by
  have h (j' : ι') : ((S.map (e.extendFunctor C)).map
      (HomologicalComplex.eval C c' j')).ShortExact := by
    by_cases hj' : ∃ j, e.f j = j'
    · obtain ⟨j, hj⟩ := hj'
      let := hS.mono_f
      let := hS.epi_g
      exact ShortComplex.shortExact_of_iso (extendEvalIso e S hj).symm
        (hS.map (HomologicalComplex.eval C c j))
    · have h₁ := S.X₁.isZero_extend_X e j' (fun j h => hj' ⟨j,h⟩)
      have h₂ := S.X₂.isZero_extend_X e j' (fun j h => hj' ⟨j,h⟩)
      have h₃ := S.X₃.isZero_extend_X e j' (fun j h => hj' ⟨j,h⟩)
      exact { exact := ShortComplex.exact_of_isZero_X₂ _ h₂
              mono_f := h₁.mono _
              epi_g := h₃.epi _ }
  exact { exact := HomologicalComplex.exact_of_degreewise_exact _ (fun j => (h j).exact)
          mono_f := HomologicalComplex.mono_of_mono_f _ (fun j => (h j).mono_f)
          epi_g := HomologicalComplex.epi_of_epi_f _ (fun j => (h j).epi_g) }

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_LocalizingRetracts
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
namespace LittleFinitistic.DerivedSupport
universe u v
variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasColimitsOfShape (Discrete ℕ) C]
variable {X Y : C} (i : X ⟶ Y) (p : Y ⟶ X) (hip : i ≫ p = 𝟙 X)

include hip

variable [HasZeroObject C] [HasShift C ℤ]
  [∀ degree : ℤ, (shiftFunctor C degree).Additive] [Pretriangulated C]

lemma swindle_distinguished : Triangle.mk (swindleA i p) (swindleB p) 0 ∈ distTriang C := by
  apply isomorphic_distinguished _ (binaryBiproductTriangle_distinguished (∐ fun _ : ℕ => Y) X)
  refine Triangle.isoMk _ _ (Iso.refl _) (swindleIso i p hip) (Iso.refl _) ?_ ?_ ?_
  · simp only [Triangle.mk, Iso.refl_hom, binaryBiproductTriangle, Category.id_comp]
    change swindleA i p ≫ (swindleIso i p hip).hom = biprod.inl
    apply biprod.hom_ext <;> simp [swindleIso, swindleAC i p hip, swindleAB i p hip]
  · simp only [Triangle.mk, Iso.refl_hom, binaryBiproductTriangle, Category.comp_id]
    change swindleB p = (swindleIso i p hip).hom ≫ biprod.snd
    exact (biprod.lift_snd _ _).symm
  · simp
    exact (zero_comp (X := _) (f := (shiftFunctor C 1).map _)).trans (comp_zero (f := 𝟙 _)).symm

lemma localizing_of_retract (P : ObjectProperty C) [P.IsClosedUnderIsomorphisms]
    [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] (hY : P Y) : P X := by
  have h : P (∐ fun _ : ℕ => Y) := P.prop_colimit (Discrete.functor (fun _ : ℕ => Y)) (fun _ => hY)
  exact P.ext_of_isTriangulatedClosed₃ _ (swindle_distinguished i p hip) h h

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_ModuleGeneration
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBalancedTensor.leftModule _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.BlockModule.firstInflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.DirectedBound.DirectedSystem.cover_addCommGroup _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.Nakayama.coind_comm _root_.OAI.LittleFinitistic.OrdinarySimulation.TensorIdeal.leftModule _root_.OAI.LittleFinitistic.PDBarQuotient.leftModule _root_.OAI.LittleFinitistic.ProductModules.firstModule _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryEquation _root_.OAI.LittleFinitistic.QuadraticPresentation.instFiniteAuxiliaryLetter _root_.OAI.LittleFinitistic.QuadraticPresentation.step_finite _root_.OAI.LittleFinitistic.QuadraticPresentation.word_finite _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteColimits _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.inflation_preservesFiniteLimits _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.cyclicRing_finiteInst _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport
universe u w
variable {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

omit [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_shortExact₁ (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    (h₂ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₂))
    (h₃ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    P ((DerivedCategory.singleFunctor _ 0).obj S.X₁) := by
  let := hS.mono_f
  let := hS.epi_g
  let F := HomologicalComplex.single (ModuleCat R) (.up ℤ) 0
  let e := DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0
  apply P.prop_of_iso (e.app S.X₁).symm
  exact P.ext_of_isTriangulatedClosed₁ _
    (DerivedCategory.triangleOfSES_distinguished (hS.map F))
    (P.prop_of_iso (e.app S.X₂) h₂) (P.prop_of_iso (e.app S.X₃) h₃)

omit [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_shortExact₂ (S : ShortComplex (ModuleCat R)) (hS : S.ShortExact)
    (h₁ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₁))
    (h₃ : P ((DerivedCategory.singleFunctor _ 0).obj S.X₃)) :
    P ((DerivedCategory.singleFunctor _ 0).obj S.X₂) := by
  let := hS.mono_f
  let := hS.epi_g
  let F := HomologicalComplex.single (ModuleCat R) (.up ℤ) 0
  let e := DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0
  apply P.prop_of_iso (e.app S.X₂).symm
  exact P.ext_of_isTriangulatedClosed₂ _
    (DerivedCategory.triangleOfSES_distinguished (hS.map F))
    (P.prop_of_iso (e.app S.X₁) h₁) (P.prop_of_iso (e.app S.X₃) h₃)

omit [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_single_of_cofan {I : Type u} [P.IsClosedUnderColimitsOfShape (Discrete I)]
    {M : I → ModuleCat R} (s : Cofan M) (hs : IsColimit s)
    (hM : ∀ i, P ((DerivedCategory.singleFunctor _ 0).obj (M i))) :
    P ((DerivedCategory.singleFunctor _ 0).obj s.pt) := by
  let F := HomologicalComplex.single (ModuleCat R) (.up ℤ) 0
  let e := DerivedCategory.singleFunctorIsoCompQ (ModuleCat R) 0
  have hs' := isColimitCofanMkObjOfIsColimit F M s.inj hs
  apply P.prop_of_iso (e.app s.pt).symm
  exact P.prop_of_isColimit (derivedCofanIsColimit _ hs')
    (fun i => P.prop_of_iso (e.app (M i.as)) (hM i.as))

variable {S : Type u} [Ring S] (χ : R →+* S)
variable (hcop : ∀ I : Type u, P.IsClosedUnderColimitsOfShape (Discrete I))
include hcop

lemma prop_restricted_projective (M : ModuleCat.{u} S) [Module.Projective S M]
    (hS : P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars χ).obj (ModuleCat.of S S)))) :
    P ((DerivedCategory.singleFunctor _ 0).obj ((ModuleCat.restrictScalars χ).obj M)) := by
  classical
  let F := ModuleCat.restrictScalars χ ⋙ DerivedCategory.singleFunctor (ModuleCat R) 0
  let := hcop M
  obtain ⟨s, hs⟩ := (Module.projective_def' (R := S) (P := M)).mp inferInstance
  let q : ModuleCat.of S (M →₀ S) ⟶ M := ModuleCat.ofHom (Finsupp.linearCombination S id)
  let j : M ⟶ ModuleCat.of S (M →₀ S) := ModuleCat.ofHom s
  have hjq : j ≫ q = 𝟙 _ := by ext x; exact congrFun (congrArg DFunLike.coe hs) x
  apply localizing_of_retract (F.map j) (F.map q) (by rw [← F.map_comp, hjq, F.map_id]) P
  let cs : Cofan (fun _ : M => ModuleCat.of S S) :=
    Cofan.mk (ModuleCat.of S (M →₀ S)) (fun x => ModuleCat.ofHom (Finsupp.lsingle x))
  have hc : IsColimit cs := by
    refine Cofan.IsColimit.mk _
      (fun t => ModuleCat.ofHom (Finsupp.lsum ℤ (fun x => (t.inj x).hom))) ?_ ?_
    · intro t x
      ext
      simp [cs]
    · intro t f hf
      apply ModuleCat.hom_ext
      apply Finsupp.lhom_ext'
      intro x
      simpa [cs] using congrArg ModuleCat.Hom.hom (hf x)
  let G := ModuleCat.restrictScalars χ
  exact prop_single_of_cofan P (Cofan.mk (G.obj cs.pt) (fun x => G.map (cs.inj x)))
    (isColimitCofanMkObjOfIsColimit G _ cs.inj hc) (fun _ => hS)

omit hcop [HasDerivedCategory.{w} (ModuleCat.{u} R)] in
lemma submodule_shortExact (M : ModuleCat.{u} R) (N : Submodule R M) :
    (ShortComplex.mk (ModuleCat.ofHom N.subtype) (ModuleCat.ofHom N.mkQ)
      (by ext x; exact (Submodule.Quotient.mk_eq_zero N).mpr x.property)).ShortExact where
  mono_f := (ModuleCat.mono_iff_injective _).mpr N.injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr N.mkQ_surjective
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    exact ⟨⟨x, (Submodule.Quotient.mk_eq_zero N).mp hx⟩, rfl⟩

variable (J : Ideal R) [J.IsTwoSided] [IsSemisimpleRing (R ⧸ J)]

lemma prop_annihilated_module
    (hQ : P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of (R ⧸ J) (R ⧸ J)))))
    (M : ModuleCat.{u} R) (hM : Module.IsTorsionBySet R M J) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let := hM.module
  let M' := ModuleCat.of (R ⧸ J) M
  let : Module.Projective (R ⧸ J) M' := Module.projective_of_isSemisimpleRing _ _
  have h := prop_restricted_projective P (Ideal.Quotient.mk J) hcop M' hQ
  let e : ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj M') ≅ M :=
    LinearEquiv.toModuleIso {
      toFun := id
      invFun := id
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun r x => hM.mk_smul r x }
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e) h

lemma prop_of_nilpotent_kernel
    (hQ : P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk J)).obj (ModuleCat.of (R ⧸ J) (R ⧸ J)))))
    (hJ : ∃ n : ℕ, J ^ n = ⊥) (M : ModuleCat.{u} R) :
    P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  have aux (n : ℕ) (M : ModuleCat.{u} R) (hn : J^n • (⊤ : Submodule R M) = ⊥) :
      P ((DerivedCategory.singleFunctor _ 0).obj M) := by
    induction n generalizing M with
    | zero =>
      have hm : (⊤ : Submodule R M) = ⊥ := by
        simpa only [Submodule.pow_zero, Ideal.one_eq_top, Submodule.top_smul] using hn
      apply P.prop_of_isZero
      apply (DerivedCategory.singleFunctor _ 0).map_isZero
      rw [ModuleCat.isZero_iff_subsingleton]
      exact (Submodule.subsingleton_iff R).mp (subsingleton_of_bot_eq_top hm.symm)
    | succ n ih =>
      let N : Submodule R M := J • ⊤
      have hn' : J^n • (⊤ : Submodule R N) = ⊥ := by
        apply Submodule.map_injective_of_injective N.injective_subtype
        rw [Submodule.map_bot, Submodule.map_smul'', Submodule.map_subtype_top]
        change J^n • (J • (⊤ : Submodule R M)) = ⊥
        rw [← Submodule.mul_smul, ← Submodule.pow_succ]
        exact hn
      apply prop_single_shortExact₂ P _ (submodule_shortExact M N)
      · exact ih (ModuleCat.of R N) hn'
      · exact prop_annihilated_module P hcop J hQ (ModuleCat.of R (M ⧸ N))
          (Module.isTorsionBySet_quotient_ideal_smul M J)
  obtain ⟨n, hn⟩ := hJ
  exact aux n M (by simp [hn])

variable {k ι : Type u} [Field k] [Fintype ι] (ψ : R →+* (ι → k))

omit [P.IsTriangulated] [P.IsClosedUnderColimitsOfShape (Discrete ℕ)] in
lemma prop_restricted_pi
    (hcoord : ∀ j, P ((DerivedCategory.singleFunctor _ 0).obj (coordinateModule ψ j))) :
    P ((DerivedCategory.singleFunctor _ 0).obj
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k)))) := by
  classical
  let := hcop ι
  let Z := coordinateModule ψ
  have h := prop_single_of_cofan P (ModuleCat.coproductCocone Z)
    (ModuleCat.coproductCoconeIsColimit Z) hcoord
  let e₁ : (Π₀ i, Z i) ≃ₗ[R] (∀ i, Z i) := DFinsupp.linearEquivFunOnFintype
  let e₂ : (∀ i, Z i) ≃ₗ[R]
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k))) := {
    toFun := fun x i => x i
    invFun := fun x i => x i
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso
    ((e₁.trans e₂).toModuleIso)) h

lemma prop_all_of_product_augmentation (hψ : Function.Surjective ψ)
    (hnil : ∃ n : ℕ, (RingHom.ker ψ)^n = ⊥)
    (hcoord : ∀ j, P ((DerivedCategory.singleFunctor _ 0).obj (coordinateModule ψ j)))
    (M : ModuleCat.{u} R) : P ((DerivedCategory.singleFunctor _ 0).obj M) := by
  let e := RingHom.quotientKerEquivOfSurjective hψ
  let : IsSemisimpleRing (R ⧸ RingHom.ker ψ) := e.isSemisimpleRing_iff.mpr inferInstance
  apply prop_of_nilpotent_kernel P hcop (RingHom.ker ψ) _ hnil M
  let e' : ((ModuleCat.restrictScalars (Ideal.Quotient.mk (RingHom.ker ψ))).obj
      (ModuleCat.of (R ⧸ RingHom.ker ψ) (R ⧸ RingHom.ker ψ))) ≅
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k))) :=
    LinearEquiv.toModuleIso (show
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (RingHom.ker ψ))).obj
        (ModuleCat.of (R ⧸ RingHom.ker ψ) (R ⧸ RingHom.ker ψ))) ≃ₗ[R]
      ((ModuleCat.restrictScalars ψ).obj (ModuleCat.of (ι → k) (ι → k))) from {
      toFun := e
      invFun := e.symm
      left_inv := e.left_inv
      right_inv := e.right_inv
      map_add' := e.map_add
      map_smul' := fun r x => by
        change e (Ideal.Quotient.mk (RingHom.ker ψ) r * (show R ⧸ RingHom.ker ψ from x)) = ψ r * e x
        rw [e.map_mul]
        rfl })
  exact P.prop_of_iso ((DerivedCategory.singleFunctor _ 0).mapIso e'.symm)
    (prop_restricted_pi P hcop ψ hcoord)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Derived_UpperTruncation
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteColimits _root_.OAI.LittleFinitistic.restrictScalars_preservesFiniteLimits
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits
open HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex

open CategoryTheory CategoryTheory.Limits HomologicalComplex
namespace LittleFinitistic.DerivedSupport

section
universe u
variable {R : Type u} [Ring R]

lemma upper_isZero_X (K : CochainComplex (ModuleCat.{u} R) ℤ) (a j : ℤ) (hj : a < j) :
    IsZero ((upper K a).X j) := by
  apply ModuleCat.isZero_iff_subsingleton.2
  change Subsingleton (upperSub K a j)
  simp only [upperSub, show ¬ j < a by omega, ↓reduceIte, show ¬ j = a by omega]
  infer_instance

end

universe u w
variable {R : Type u} [Ring R]
variable (K : CochainComplex (ModuleCat.{u} R) ℤ)

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} R)))
  [P.IsTriangulated] [P.IsClosedUnderIsomorphisms]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]

lemma prop_of_all_modules
    (hM : ∀ (M : ModuleCat R), P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M)) :
    P (DerivedCategory.Q.obj K) := by
  exact localizing_sequence_colimit (fun n => upper K (n : ℤ)) (upperSequenceMap K)
    (upperSequenceCocone K) (upperSequenceIsColimit K) P (fun n =>
      prop_of_boundedAbove_terms P (upper K _) n (upper_isZero_X K _) (fun j => hM _))

lemma localizing_eq_top_of_all_modules
    (hM : ∀ (M : ModuleCat R), P ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj M))
    (X : DerivedCategory (ModuleCat R)) : P X := by
  exact P.prop_of_iso (DerivedCategory.Q.objObjPreimageIso X)
    (prop_of_all_modules (DerivedCategory.Q.objPreimage X) P hM)

end LittleFinitistic.DerivedSupport

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Socle
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instModuleT _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instSMulT _root_.OAI.LittleFinitistic.CummingsConstruction.newRegularπ_epi _root_.OAI.LittleFinitistic.CummingsConstruction.periodicAug_quasiIso _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace CummingsConstruction
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]

variable (χ : C →ₐ[k] (ι → k))

lemma augmentation_surjective (hχ : Function.Surjective χ) : Function.Surjective (augmentation χ) := by
  intro v
  obtain ⟨c, hc⟩ := hχ (v ∘ Sum.inl)
  refine ⟨((c, fun i => TrivSqZeroExt.inl (v (.inr i))), 0), ?_⟩
  ext i
  cases i with
  | inl i => exact congrFun hc i
  | inr i => rfl

end CummingsConstruction
end LittleFinitistic
end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Augmentation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instModuleT _root_.OAI.LittleFinitistic.CummingsConstruction.NewInjective.instSMulT _root_.OAI.LittleFinitistic.CummingsConstruction.newRegularπ_epi _root_.OAI.LittleFinitistic.CummingsConstruction.periodicAug_quasiIso _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CummingsConstruction.cval_mul _root_.OAI.LittleFinitistic.CummingsConstruction.ehead_mul _root_.OAI.LittleFinitistic.CummingsConstruction.epsDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.etail_mul _root_.OAI.LittleFinitistic.CummingsConstruction.newDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.oval_mul
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open CategoryTheory
namespace LittleFinitistic
universe u
variable (A : Type u) [Ring A]
namespace CummingsConstruction
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k))
lemma mem_ker_augmentation (x : T χ) :
    x ∈ RingHom.ker (augmentation χ).toRingHom ↔ χ x.fst.1 = 0 ∧ newAugmentation x.fst.2 = 0 := by
  change (Sum.elim (χ x.fst.1) (newAugmentation x.fst.2) : Sum ι ι → k) = 0 ↔ _
  constructor
  · intro h
    exact ⟨funext fun i => congrFun h (.inl i), funext fun i => congrFun h (.inr i)⟩
  · rintro ⟨h₁, h₂⟩
    ext i
    cases i <;> simp [h₁, h₂]

lemma ker_square_pureOldRadical :
    (RingHom.ker (augmentation χ).toRingHom) ^ 2 ≤ pureOldRadical χ := by
  rw [Submodule.pow_succ, Submodule.pow_one]
  apply Ideal.mul_le.mpr
  intro x hx y hy
  obtain ⟨hxc, hxe⟩ := (mem_ker_augmentation χ x).mp hx
  obtain ⟨hyc, hye⟩ := (mem_ker_augmentation χ y).mp hy
  change x.fst.2 * y.fst.2 = 0 ∧
    newAugmentation x.fst.2 * SimpleSum.value (TriangularConstruction.offValue y.snd) +
      χ y.fst.1 * SimpleSum.value (TriangularConstruction.offValue x.snd) = 0 ∧ χ (x.fst.1 * y.fst.1) = 0
  refine ⟨?_, by simp [hxe, hyc], by simp [map_mul, hxc]⟩
  ext i : 1
  have hx0 : (x.fst.2 i).fst = 0 := congrFun hxe i
  have hy0 : (y.fst.2 i).fst = 0 := congrFun hye i
  apply TrivSqZeroExt.ext <;> simp [hx0, hy0]

lemma pow_le_comap_pow_noncomm {R S : Type*} [Ring R] [Ring S] (f : R →+* S)
    (I : Ideal R) (J : Ideal S) (h : I ≤ J.comap f) (n : ℕ) : I ^ n ≤ (J ^ n).comap f := by
  induction n with
  | zero => simp [Submodule.pow_zero, Ideal.one_eq_top]
  | succ n ih =>
    rw [Submodule.pow_succ, Submodule.pow_succ]
    apply Ideal.mul_le.mpr
    intro x hx y hy
    change f (x * y) ∈ J ^ n * J
    rw [map_mul]
    exact Ideal.mul_mem_mul (ih hx) (h hy)

lemma augmentation_ker_nilpotent (hJ : ∃ n : ℕ, (RingHom.ker χ.toRingHom) ^ n = ⊥) :
    ∃ n : ℕ, (RingHom.ker (augmentation χ).toRingHom) ^ n = ⊥ := by
  obtain ⟨n, hn⟩ := hJ
  let K := RingHom.ker (augmentation χ).toRingHom
  let J := RingHom.ker χ.toRingHom
  have hcomap : K ≤ J.comap (TriangularConstruction.toC C (NewCorner k ι) (SimpleSum χ)) := by
    intro x hx
    exact ((mem_ker_augmentation χ x).mp hx).1
  have hpow := pow_le_comap_pow_noncomm _ K J hcomap (n + 2)
  have hjn : J ^ (n + 2) = ⊥ := by
    apply le_bot_iff.mp
    exact (Ideal.pow_le_pow_right (I := J) (Nat.le_add_right n 2)).trans hn.le
  rw [hjn] at hpow
  refine ⟨n + 2, le_bot_iff.mp ?_⟩
  intro x hx
  have hc : x.fst.1 = 0 := hpow hx
  have hp := ker_square_pureOldRadical χ ((Ideal.pow_le_pow_right (I := K) (by omega : 2 ≤ n + 2)) hx)
  change x = 0
  apply TrivSqZeroExt.ext
  · exact Prod.ext hc hp.1
  · exact hp.2.1

end CummingsConstruction
end LittleFinitistic

end
end
end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_InjectiveCorners
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.CummingsConstruction.newRegularπ_epi _root_.OAI.LittleFinitistic.CummingsConstruction.periodicAug_quasiIso _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom _root_.OAI.LittleFinitistic.CummingsConstruction.epsDifferential_sq _root_.OAI.LittleFinitistic.CummingsConstruction.newDifferential_sq
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory
namespace LittleFinitistic.CummingsConstruction

section
open CategoryTheory
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι) [DecidableEq ι]

lemma field_module_injective (V : ModuleCat.{u} k) : Injective V where
  factors {X Y} g f hf := by
    obtain ⟨s, hs⟩ := f.hom.exists_leftInverse_of_injective
      (LinearMap.ker_eq_bot.mpr ((ModuleCat.mono_iff_injective f).mp hf))
    refine ⟨ModuleCat.ofHom (g.hom.comp s), ?_⟩
    apply ModuleCat.hom_ext
    change g.hom.comp (s.comp f.hom) = g.hom
    rw [hs, LinearMap.comp_id]

instance coindField_injective : Injective (coindField χ) :=
  (ModuleCat.restrictCoextendScalarsAdj (algebraMap k (T χ))).map_injective _
    (field_module_injective (ModuleCat.of k k))

end

open CategoryTheory
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι) [DecidableEq ι]

omit [DecidableEq ι] in
lemma newInjectiveInclusion_apply (x : NewInjective χ i) (r : T χ) :
    (newInjectiveInclusion χ i x) r = (NewInjective.act χ i r x).2.2 := by
  change (ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction _
    (lastCoordinate χ i)).hom x r = _
  rw [ModuleCat.RestrictionCoextensionAdj.HomEquiv.fromRestriction_hom_apply_apply]
  change (r • x : NewInjective χ i).2.2 = _
  rfl

lemma newInjectiveInclusion_retraction :
    newInjectiveInclusion χ i ≫ newInjectiveRetraction χ i = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (newInjectiveRetraction χ i (newInjectiveInclusion χ i x)) = x
  apply NewInjective.ext (χ := χ) (i := i)
  · change (newInjectiveInclusion χ i x) (socle χ (.inl i)) = x.1
    rw [newInjectiveInclusion_apply]
    change (NewInjective.act χ i (socle χ (.inl i)) x).2.2 = x.1
    change (Pi.single (M := fun _ : ι => k) i 1) i * x.1 + 0 * x.2.1 + 0 * x.2.2 = x.1
    simp
  · change (newInjectiveInclusion χ i x) (socle χ (.inr i)) = x.2.1
    rw [newInjectiveInclusion_apply]
    change (NewInjective.act χ i (socle χ (.inr i)) x).2.2 = x.2.1
    simp [NewInjective.act, NewInjective.value, oval, etail, ehead, socle, TriangularConstruction.offValue, SimpleSum.value]
    try exact Or.inl rfl
  · change (newInjectiveInclusion χ i x) (newIdem χ i) = x.2.2
    rw [newInjectiveInclusion_apply]
    change (NewInjective.act χ i (newIdem χ i) x).2.2 = x.2.2
    simp [NewInjective.act, NewInjective.value, oval, etail, ehead, newIdem, TriangularConstruction.offValue, SimpleSum.value]
    exact Or.inl rfl

lemma newInjective_injective : Injective (ModuleCat.of (T χ) (NewInjective χ i)) := by
  exact (show CategoryTheory.Retract (ModuleCat.of (T χ) (NewInjective χ i))
    (coindField χ) from ⟨newInjectiveInclusion χ i, newInjectiveRetraction χ i,
      newInjectiveInclusion_retraction χ i⟩).injective

end LittleFinitistic.CummingsConstruction

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_InjectiveResolution
attribute [-instance] _root_.OAI.DerivedBar.Multibar.patternModule _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.DerivedBar.termModule _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleBarComparison.outsideModule _root_.OAI.LittleFinitistic.BimoduleCoefficients.instAddCommGroupCarrierTensorProductMulOpposite _root_.OAI.LittleFinitistic.BimoduleCoefficients.instModuleCarrierTensorProductMulOpposite_1 _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedSupport.derivedHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyHasCoproducts _root_.OAI.LittleFinitistic.DerivedSupport.homotopyQuasiIsoCoproducts _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory
namespace LittleFinitistic.CummingsConstruction
open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

lemma newRegular_exact :
    (ShortComplex.mk (newRegularι χ i) (newInjectiveπ χ i) (newRegularι_π χ i)).ShortExact where
  mono_f := by
    rw [ModuleCat.mono_iff_injective]
    intro x y h
    apply TrivSqZeroExt.ext
    · exact congrArg (fun z : NewInjective χ i => z.2.1) h
    · exact congrArg (fun z : NewInjective χ i => z.2.2) h
  epi_g := by
    rw [ModuleCat.epi_iff_surjective]
    intro a
    exact ⟨(a,0,0), rfl⟩
  exact := by
    rw [ShortComplex.moduleCat_exact_iff]
    intro x hx
    refine ⟨(x.2.1,x.2.2), ?_⟩
    apply NewInjective.ext (χ := χ) (i := i)
    · exact hx.symm
    · rfl
    · rfl

lemma periodic_shortExact :
    (ShortComplex.mk (periodicι χ i) (periodicπ χ i) (periodicι_π χ i)).ShortExact where
  mono_f := HomologicalComplex.mono_of_mono_f _ (fun _ => (newRegular_exact χ i).mono_f)
  epi_g := HomologicalComplex.epi_of_epi_f _ (fun _ => (newRegular_exact χ i).epi_g)
  exact := HomologicalComplex.exact_of_degreewise_exact _ (fun _ => (newRegular_exact χ i).exact)

end LittleFinitistic.CummingsConstruction

end

end OAI
end

section
-- module Solutions.Q221_FA.FinitisticAsymmetry_Triangular_Generation
attribute [-instance] _root_.OAI.DerivedBar.finiteTotalDiagonal _root_.OAI.DerivedBar.fintypeTotalDiagonal _root_.OAI.ExternalTensor.Section4.rightBinaryBiproducts _root_.OAI.ExternalTensor.Section4.rightFiniteBiproducts _root_.OAI.ExternalTensor.Section4.rightModuleK _root_.OAI.LittleFinitistic.BimoduleTotal.restrictPreservesHomology _root_.OAI.LittleFinitistic.DerivedTruncation.lower_isLE_minus_one _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomModule _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiHomSMul _root_.OAI.LittleFinitistic.FormalSummandAction.karoubiLinear _root_.OAI.LittleFinitistic.LeftVertexHomology.scalarTower _root_.OAI.LittleFinitistic.QuadraticEncoding.completedExtensionAdditive _root_.OAI.LittleFinitistic.QuadraticEncoding.karoubiExtensionAdditive _root_.OAI.LittleFinitistic.SelectedFirstBlockFamily.derivedInflation_additive _root_.OAI.LittleFinitistic.SelectionEncoding.instRingDirectedAlgebra _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instAddCommGroup _root_.OAI.LittleFinitistic.ThreeVertexAlgebra.instRing _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.kernelRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroRetracts _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroShift _root_.OAI.LittleFinitistic.TwoConeVerdier.ConePair.zeroTriangulated
attribute [-simp] _root_.OAI.ExternalTensor.Section4.sum_hom
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated HomologicalComplex
namespace LittleFinitistic.CummingsConstruction
universe u w
variable {k C ι : Type u} [Field k] [Ring C] [Algebra k C]
variable (χ : C →ₐ[k] (ι → k)) (i : ι)

lemma oldSingleι_π (n : ℕ) : oldSingleι χ i n ≫ oldSingleπ χ i n = 𝟙 _ := by
  apply from_single_hom_ext
  simp [oldSingleι, oldSingleπ]
  erw [mkHomFromSingle_f, mkHomToSingle_f, Category.comp_id, Category.id_comp,
    Iso.hom_inv_id]

variable [HasDerivedCategory.{w} (ModuleCat.{u} (T χ))]

omit [HasDerivedCategory (ModuleCat (T χ))] in
lemma extended_shortExact :
    ((ShortComplex.mk (periodicι χ i) (periodicπ χ i) (periodicι_π χ i)).map
      (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat (T χ)))).ShortExact :=
  DerivedSupport.extend_shortExact _ _ (periodic_shortExact χ i)

variable (P : ObjectProperty (DerivedCategory (ModuleCat.{u} (T χ))))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [P.IsClosedUnderColimitsOfShape (Discrete ℕ)]
  (hI : ∀ M : ModuleCat.{u} (T χ), Injective M →
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj M))

include hI

lemma extendedInjective_mem [DecidableEq ι] : P (DerivedCategory.Q.obj (extendedInjective χ i)) := by
  apply DerivedSupport.prop_of_boundedAbove_terms P _ 0
  · intro j hj
    exact CochainComplex.isZero_of_isStrictlyLE _ 0 j hj
  · intro j
    apply hI
    by_cases hj : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = j
    · obtain ⟨n, hn⟩ := hj
      exact Injective.of_iso ((periodicInjective χ i).extendXIso _ hn).symm
        (newInjective_injective χ i)
    · exact (isZero_extend_X _ _ j (fun n hn => hj ⟨n,hn⟩)).injective

lemma oldSimple_shifted_retract [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) (-2)).obj (oldSimple χ i)) := by
  let S := (ShortComplex.mk (periodicι χ i) (periodicπ χ i) (periodicι_π χ i)).map
    (ComplexShape.embeddingDownNat.extendFunctor (ModuleCat (T χ)))
  let hS := extended_shortExact χ i
  let Δ := DerivedCategory.triangleOfSES hS
  have hΔ : Δ ∈ distTriang _ := DerivedCategory.triangleOfSES_distinguished hS
  let F := ComplexShape.embeddingDownNat.extendFunctor (ModuleCat (T χ)) ⋙ DerivedCategory.Q
  let j := F.map (oldSingleι χ i 2)
  let p := F.map (oldSingleπ χ i 2)
  have hjp : j ≫ p = 𝟙 _ := by
    dsimp [j,p]
    rw [← F.map_comp, oldSingleι_π, F.map_id]
  have hzero : j ≫ Δ.mor₃ = 0 := by
    have hle : (DerivedCategory.TStructure.t (C := ModuleCat (T χ))).IsLE (F.obj _) (-2) :=
      DerivedCategory.TStructure.t.isLE_of_iso (oldSingleDerivedIso χ i 2).symm (-2)
    have hge : (DerivedCategory.TStructure.t (C := ModuleCat (T χ))).IsGE Δ.obj₁ 0 :=
      DerivedCategory.TStructure.t.isGE_of_iso (regularDerivedIso χ i).symm 0
    have hges := DerivedCategory.TStructure.t.isGE_shift Δ.obj₁ 0 1 (-1) (by omega)
    exact DerivedCategory.TStructure.t.zero (j ≫ Δ.mor₃) (-2) (-1) (by omega)
  obtain ⟨l, hl⟩ := Triangle.coyoneda_exact₃ Δ hΔ j hzero
  have hlp : l ≫ (Δ.mor₂ ≫ p) = 𝟙 _ := by erw [← Category.assoc, ← hl, hjp]
  apply P.prop_of_iso (oldSingleDerivedIso χ i 2)
  exact DerivedSupport.localizing_of_retract l (Δ.mor₂ ≫ p) hlp P
    (extendedInjective_mem χ i P hI)

lemma oldSimple_mem [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (oldSimple χ i)) := by
  apply P.prop_of_iso (((DerivedCategory.singleFunctors (ModuleCat (T χ))).shiftIso
    (-2) 0 (-2) (by omega)).app (oldSimple χ i))
  exact P.le_shift (-2) _ (oldSimple_shifted_retract χ i P hI)

lemma newRegular_mem [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (newRegular χ i)) := by
  exact DerivedSupport.prop_single_shortExact₁ P _ (newRegular_exact χ i)
    (hI _ (newInjective_injective χ i)) (oldSimple_mem χ i P hI)

lemma newSimple_mem [DecidableEq ι] :
    P ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).obj (newSimple χ i)) := by
  apply P.prop_of_iso (regularDerivedIso χ i)
  apply DerivedSupport.prop_of_boundedAbove_terms P _ 0
  · intro j hj
    exact CochainComplex.isZero_of_isStrictlyLE _ 0 j hj
  · intro j
    by_cases hj : ∃ n : ℕ, ComplexShape.embeddingDownNat.f n = j
    · obtain ⟨n, hn⟩ := hj
      apply P.prop_of_iso ((DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).mapIso
        ((periodicRegular χ i).extendXIso _ hn).symm)
      exact newRegular_mem χ i P hI
    · apply P.prop_of_isZero
      apply (DerivedCategory.singleFunctor (ModuleCat (T χ)) 0).map_isZero
      exact isZero_extend_X _ _ j (fun n hn => hj ⟨n,hn⟩)

omit hI [HasDerivedCategory.{w} (ModuleCat.{u} (T χ))] in
lemma injectivesGenerate_oai [Fintype ι] (hχ : Function.Surjective χ)
    (hnil : ∃ n : ℕ, (RingHom.ker χ.toRingHom)^n = ⊥) :
    InjectivesGenerate (T χ) := by
  classical
  let := HasDerivedCategory.standard (ModuleCat.{u} (T χ))
  intro P hP hT hcop hI X
  let := hP
  let := hT
  let (I : Type u) := hcop I
  let : P.IsClosedUnderColimitsOfShape (Discrete ℕ) :=
    ObjectProperty.IsClosedUnderColimitsOfShape.of_equivalence
      (Discrete.equivalence (Equiv.ulift : ULift.{u} ℕ ≃ ℕ))
  apply DerivedSupport.localizing_eq_top_of_all_modules P
  · intro M
    apply DerivedSupport.prop_all_of_product_augmentation P hcop
      (augmentation χ).toRingHom (augmentation_surjective χ hχ)
      (augmentation_ker_nilpotent χ hnil) _ M
    intro j
    cases j with
    | inl i => exact oldSimple_mem χ i P hI
    | inr i => exact newSimple_mem χ i P hI

end LittleFinitistic.CummingsConstruction

end

end OAI
end

theorem solution.{u} : type_of% @OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate_oai.{u} := @OAI.LittleFinitistic.CummingsConstruction.injectivesGenerate_oai.{u}
