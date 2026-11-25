-- Prove2me | solution 1 for GlobalTheory.SS.WeakNeronEx.exists_weakNeron
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:53:12.606175+00:00
-- url     : https://prove2.me/submissions/fee0bee9-99af-4e39-bd93-89ba0af926fb

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_OfDerivationFnOn
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_PlOrdSomeOfAssociated
import Definitions.Def_Development_AbelianVarietyTheory_Statements_SemistableTorsion_SemistableFin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SmoothFlatAlgebraFiniteCoverDecompStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSchemeModelOfAffineSmoothChartStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCoverModelIrreducibleSpecialFibreStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsWeakNeronModel
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_sp_comp
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_smooth_away
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_exists_affine
import Theorems.Thm_GlobalTheory_SS_WeakNeronEx_range_subset
import Theorems.Thm_GlobalTheory_SS_Smoothening_Cov_trans
import Theorems.Thm_GlobalTheory_T_exists_cover_model_irreducible_specialFibre
import Theorems.Thm_GlobalTheory_T_exists_scheme_model_of_affine_smooth_chart
import Theorems.Thm_GlobalTheory_T_smooth_flat_algebra_finite_cover_decomp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SS GlobalTheory.SS.WeakNeronEx
open GlobalTheory.AbLaw ReciprocityTheory.ChartRestriction.G.Out
namespace GlobalTheory.SS.WeakNeronEx
theorem _root_.solution : ∀ (R K : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K] [IsFractionRing R K], PerfectField (IsLocalRing.ResidueField R) → ∀ (A : Over (Sp K)), Smooth A.hom → IsProper A.hom → GlobalTheory.AbLaw.IsProjBy A.hom → ∃ (n : ℕ) (M : Fin n → Model R A), (∀ i, (M i).Irr) ∧ WeakNeron M := by
  intro R K _ _ _ _ _ _ hperf A hsm hpr hproj
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  obtain ⟨m, B, _, _, u, hB, hpt⟩ := exists_affine R K A.hom hproj
  have hs : ∀ i, Algebra.Smooth R (Localization.Away (algebraMap R (B i) π)) := fun i => by
    obtain ⟨-, -, h₃, h₄⟩ := hB i
    have h₅ : Smooth (spMap (algebraMap K (TensorProduct R K (B i)))) := by rw [← h₄]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)] at h₅
    haveI := RingHom.smooth_algebraMap.mp h₅
    exact smooth_away R K hπ (B i)
  have h₁ := fun i => by
    haveI := (hB i).1
    haveI := (hB i).2.1
    exact GlobalTheory.T.smooth_flat_algebra_finite_cover_decomp R K π hπ hperf (B i) (hs i)
  choose n C instR instA φ hC hlift using h₁
  have h₂ := fun i k => GlobalTheory.T.exists_scheme_model_of_affine_smooth_chart R K A hsm inferInstance inferInstance (C i k) (hC i k).1
    (spMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom ≫ u i)
    (by haveI := (hC i k).2; haveI := (hB i).2.2.1; infer_instance)
    (by
      rw [Category.assoc, (hB i).2.2.2, sp_comp]
      exact congrArg spMap (AlgHom.comp_algebraMap (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k))))
  choose M g hg₁ hg₂ hg₃ hg₄ using h₂
  choose p N q hN hcov using fun i k => GlobalTheory.T.exists_cover_model_irreducible_specialFibre R K A (M i k)
  let e := Fintype.equivFin (Σ (i : Fin m) (k : Fin (n i)), Fin (p i k))
  refine ⟨_, fun t => N (e.symm t).1 (e.symm t).2.1 (e.symm t).2.2, fun t => (hN _ _ _).1, ?_⟩
  intro V L _ _ _ _ _ _ _ hmax a ha
  suffices h : ∃ i k l, ∃ b : Sp V ⟶ (N i k l).Y.left, b ≫ (N i k l).Y.hom = spMap (algebraMap R V) ∧
      spMap (algebraMap V L) ≫ b = a ≫ (N i k l).j by
    obtain ⟨i, k, l, h⟩ := h
    refine ⟨e ⟨i, k, l⟩, ?_⟩
    beta_reduce
    rw [e.symm_apply_apply]
    exact h
  have hunr : Unr π V := by
    refine ⟨inferInstance, inferInstance, ?_⟩
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← hmax, hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]
  obtain ⟨i, b, ψ, hψ, hb⟩ := hpt V L a ha
  obtain ⟨k, c, hc⟩ := hlift i V b hunr
  have hb₀ : (spMap c.toRingHom ≫ g i k) ≫ (M i k).Y.hom = spMap (algebraMap R V) := by
    rw [Category.assoc, hg₂, sp_comp]
    exact congrArg spMap (AlgHom.comp_algebraMap c)
  have hgen : spMap (algebraMap V L) ≫ spMap c.toRingHom ≫ g i k = a ≫ (M i k).j := by
    letI : Algebra R L := ((algebraMap V L).comp (algebraMap R V)).toAlgebra
    haveI : IsScalarTower R V L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    let ψ₀ : TensorProduct R K (B i) →ₐ[R] L := ⟨ψ, fun x => by
      have := hb (algebraMap R _ x)
      rw [AlgHom.commutes] at this
      refine Eq.trans (congrArg ψ ?_) this
      exact ((Algebra.TensorProduct.includeRight : B i →ₐ[R] TensorProduct R K (B i)).commutes x).symm⟩
    let ψ' : TensorProduct R K (C i k) →ₐ[R] L := Algebra.TensorProduct.lift
      (ψ₀.comp Algebra.TensorProduct.includeLeft) ((IsScalarTower.toAlgHom R V L).comp c) fun _ _ => Commute.all _ _
    have e₁ : ψ'.toRingHom.comp (Algebra.TensorProduct.map (AlgHom.id K K) (φ i k)).toRingHom = ψ := by
      refine RingHom.ext fun x => ?_
      induction x using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add, hx, hy]
      | tmul x y =>
        have h₅ : c (φ i k y) = b y := congrArg (fun q => q y) hc
        show ψ' (x ⊗ₜ φ i k y) = _
        rw [Algebra.TensorProduct.lift_tmul]
        show ψ (x ⊗ₜ 1) * algebraMap V L (c (φ i k y)) = _
        rw [h₅, ← hb, ← map_mul, Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
    have e₂ : ψ'.toRingHom.comp (Algebra.TensorProduct.includeRight : C i k →ₐ[R] TensorProduct R K (C i k)).toRingHom =
        (algebraMap V L).comp c.toRingHom := by
      refine RingHom.ext fun x => ?_
      show ψ' (1 ⊗ₜ x) = _
      rw [Algebra.TensorProduct.lift_tmul, map_one, _root_.one_mul]
      rfl
    rw [← Category.assoc, sp_comp, ← e₂, ← sp_comp, Category.assoc, hg₃, ← Category.assoc, ← Category.assoc,
      sp_comp, e₁, hψ]
  have hsp : (spMap c.toRingHom ≫ g i k) (IsLocalRing.closedPoint V) ∈ (M i k).sp := by
    show (M i k).Y.hom ((spMap c.toRingHom ≫ g i k) _) = _
    rw [← Scheme.Hom.comp_apply, hb₀]
    haveI : IsLocalHom (algebraMap R V) := by
      apply ((IsLocalRing.local_hom_TFAE (algebraMap R V)).out 0 2).2
      exact hmax.le
    exact IsLocalRing.comap_closedPoint (algebraMap R V)
  obtain ⟨l, hl⟩ := hcov i k _ hsp
  obtain ⟨-, hq, hj⟩ := hN i k l
  have hfac := IsOpenImmersion.lift_fac (q i k l).left _ (range_subset _ _ hl)
  refine ⟨i, k, l, IsOpenImmersion.lift (q i k l).left _ (range_subset _ _ hl), ?_, ?_⟩
  · rw [← Over.w (q i k l), ← Category.assoc, hfac, hb₀]
  · rw [← cancel_mono (q i k l).left, Category.assoc, hfac, Category.assoc, hj, hgen]
end GlobalTheory.SS.WeakNeronEx
