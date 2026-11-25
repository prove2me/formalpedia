-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.exists_isEmbedded_of_algRes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:38:24.360419+00:00
-- url     : https://prove2.me/submissions/4a6557f9-b47b-439e-85de-0a716ab54777

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsSncModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_BlowupProjections_BlowupProjStatement
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_DivisibilityTowers_Proportional
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterAlgRes
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterPCProof
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_LocTransfer
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Immersion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterMinor
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_FiniteMinimalPrimes
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCompactEmbeddedStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionTransitionPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionCoverAndConeStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionLocalChartPolynomialStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionRegularLocalRingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncResolutionBoundaryNormalCrossingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_MetricProofs_SncModelEmbeddedLogResolution
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_isUnit_algebraMap_locRing
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_not_mem_conePts_top
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_ChartInv_isOpen_alt_bis
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_Top_isOpen_alt_bis
import Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Cmp_SncRes_sameOrbit_trans
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_exists_atlas
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_fderiv_affCoord_ker_eq_bot
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_isSNC_pullback
import Theorems.Thm_ReciprocityTheory_AnForm_R_AlgRes_volume_preimage_eq_zero
import Theorems.Thm_ReciprocityTheory_AnForm_R_eval_bind_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_mem_mcPts_iff_conePts_pC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_sameOrbit_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
theorem _root_.solution {P J : Ideal (MRing ι)} {e : ℕ} (hJ : IsMultiHomogIdeal J)
    (hJP : ¬ J ≤ P) (hPC : ∀ f : MRing ι, map (Int.castRingHom ℂ) f ∈ pC P → f ∈ P)
    (R : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) (pC J) e)
    (hsurj : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), ∃ i, ∃ x ∈ R.src i,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q)) z)
    (hinj : ∀ i j, ∀ x ∈ R.src i, ∀ x' ∈ R.src j,
      ReciprocityTheory.AnForm.R.SameOrbit (fun q => eval (R.coord i x) (R.lift i q))
        (fun q => eval (R.coord j x') (R.lift j q)) → x = x')
    (hinv : ∀ i, ∀ x ∈ R.src i, ∀ p : (k : K) → ι k, (∀ k, eval (R.coord i x) (R.lift i ⟨k, p k⟩) ≠ 0) →
      ∃ O : Set R.M, IsOpen O ∧ x ∈ O ∧ O ⊆ R.src i ∧ ∃ (q : MvPolynomial (Σ k, ι k) ℂ)
        (F : Fin (R.amb i) → MvPolynomial (Σ k, ι k) ℂ), ∀ y ∈ O,
          (∀ k, eval (R.coord i y) (R.lift i ⟨k, p k⟩) ≠ 0) ∧
          eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q ≠ 0 ∧
          ∀ l, R.coord i y l * eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) q =
            eval (ReciprocityTheory.AnForm.R.affCoord p fun q => eval (R.coord i y) (R.lift i q)) (F l)) :
    ∃ R' : AnLogRes P J e, IsEmbedded R'.A P R'.U R'.lift := by
  classical
  let R0 : ReciprocityTheory.AnForm.R.AlgRes ι (pC P) ⊤ e :=
    { M := R.M
      n := R.n
      amb := R.amb
      ideal := R.ideal
      src := R.src
      isOpen_alt_bis := R.isOpen_alt_bis
      cover := R.cover
      coord := R.coord
      isEmbedding := R.isEmbedding
      image := R.image
      trans := R.trans
      regular := R.regular
      dim := R.dim
      lift := R.lift
      lift_one := R.lift_one
      lift_mem := R.lift_mem
      compat := R.compat
      surj := fun z hz _ => hsurj z hz
      inj := fun i j x hx x' hx' _ h => hinj i j x hx x' hx' h
      inv := fun i x hx _ p hp => hinv i x hx p hp
      bd := fun _ => ⊤
      le_bd := fun _ => le_top
      zero_bd := fun i x hx =>
        ⟨fun h => absurd (h 1 Submodule.mem_top) (by simp), fun h => absurd h (not_mem_conePts_top _)⟩
      rc := 0
      comp := Fin.elim0
      sncAt := fun i x hx =>
        { r := (R.sncAt i x hx).r
          J := ∅
          h := 1
          σ := fun _ => none
          σ_injOn := by simp
          σ_eq_none := by simp
          span_eq := (R.sncAt i x hx).span_eq
          eval_h := by simp
          mem_bd := Submodule.mem_top
          le_span := fun g _ => by simp }
      comp_eq := fun i x hx => ⟨R.src i, R.isOpen_alt_bis i, hx, subset_rfl, fun k => k.elim0⟩
      mult := fun f a hf hfP hz => ⟨Fin.elim0, fun i x hx =>
        ⟨_, isUnit_algebraMap_locRing _ _ _ (by
          rw [ReciprocityTheory.AnForm.R.eval_bind_one]
          intro h0
          exact not_mem_conePts_top _ (hz _ (R.lift_mem i x hx) h0)), by simp⟩⟩ }
  obtain ⟨A, hA⟩ := R0.exists_atlas
  have hA' : R.IsGoodAtlas A := hA
  choose idx hidx using R.cover
  let R' : AnLogRes P J e :=
    { homog := hJ
      nondeg := hJP
      X := R.M
      A := A
      U := fun x => R.src (idx x)
      isOpen_U := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      lift := fun x y q => eval (R.coord (idx x) y) (R.lift (idx x) q)
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := fun x y hy => by
        rw [mem_mcPts_iff_conePts_pC]
        exact R.lift_mem (idx x) y hy
      compat := fun x x' y hy => R.compat (idx x) (idx x') y hy
      surj := fun z hz _ => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' _ hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x _ p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj
      snc := fun f a hfP hf hz => by
        have hf' : ReciprocityTheory.AnForm.R.IsMultiHomog (map (Int.castRingHom ℂ) f) a :=
          fun m hm k => hf m (support_map_subset _ _ hm) k
        have hfP' : map (Int.castRingHom ℂ) f ∉ pC P := fun h => hfP (hPC f h)
        have hz' : ∀ z ∈ ReciprocityTheory.AnForm.R.conePts (pC P), eval z (map (Int.castRingHom ℂ) f) = 0 →
            z ∈ ReciprocityTheory.AnForm.R.conePts (pC J) := by
          intro z hz1 hz2
          rw [← mem_mcPts_iff_conePts_pC] at hz1 ⊢
          exact hz z hz1 hz2
        obtain ⟨m, hm⟩ := R.isSNC_pullback A hA' idx hidx (fun _ _ => 0) _ a hf' hfP' hz'
        exact ⟨R.rc, m, R.comp, hm⟩
      null := fun j => by
        refine MeasureTheory.measure_mono_null ?_ (R.volume_preimage_eq_zero A hA' j)
        rintro y ⟨hy1, hy2⟩
        refine ⟨hy1, idx _, hidx _, ?_⟩
        simp only [Set.mem_preimage, Set.mem_ofPred_eq] at hy2 ⊢
        rw [← mem_mcPts_iff_conePts_pC]
        exact hy2 }
  refine ⟨R', ?_⟩
  exact
    { isOpen := fun x => R.isOpen_alt_bis (idx x)
      mem_U := hidx
      holo := fun x p => hA'.1 (idx x) (R.lift (idx x) p)
      mem := R'.mem
      compat := R'.compat
      surj := fun z hz => by
        rw [mem_mcPts_iff_conePts_pC] at hz
        obtain ⟨i, x, hx, hxz⟩ := hsurj z hz
        exact ⟨x, sameOrbit_trans (R.compat (idx x) i x ⟨hidx x, hx⟩) hxz⟩
      inj := fun x x' hxx => hinj (idx x) (idx x') x (hidx x) x' (hidx x') hxx
      immersion := fun x p hp j hj =>
        R0.fderiv_affCoord_ker_eq_bot A hA (idx x) x (hidx x) (not_mem_conePts_top _) p hp j hj }
end GlobalTheory.CompanionTheory.Ar.Cmp.SncRes
