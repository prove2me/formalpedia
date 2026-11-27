-- Prove2me | solution 1 for GlobalTheory.flat_of_quasiFinite_of_flat_fibres
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:38:59.203799+00:00
-- url     : https://prove2.me/submissions/ef09c360-9e49-4646-a5e4-ff6eb78a3124

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_FlatOfIsFiniteOfFinitePresentationOfFlatGeometri
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_FlatOfQuasiFiniteOfFlatFibres
import Theorems.Thm_GlobalTheory_QuasiFiniteFibreFlat_flat_away
import Theorems.Thm_GlobalTheory_IsAdicFamily_comp
import Theorems.Thm_GlobalTheory_UU_CubWeil_comp
import Theorems.Thm_GlobalTheory_UU_IsCPMap_comp
import Theorems.Thm_GlobalTheory_WeilCube_IsRatio_comp
import Theorems.Thm_GlobalTheory_ringHom_flat_of_square_of_isLocalHom
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_comm
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R A B : Type) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B] [Algebra.FinitePresentation A B] [Algebra.QuasiFinite A B] [Module.Flat R B], (∀ (k C : Type) [Field k] [CommRing C] [Algebra A C] (t : R →+* k) (h : k →+* C), (algebraMap A C).comp (algebraMap R A) = h.comp t → Module.Flat C (C ⊗[A] B)) → Module.Flat A B := by
  intro R A B _ _ _ _ _ _ _ _ _ _ H
  refine Module.flat_of_isLocalized_maximal B B (fun P ↦ Localization.AtPrime P)
    (fun P ↦ Algebra.linearMap B _) fun Q _ => ?_
  obtain ⟨A', _, _, _, P, _, _, e, -, Q', _, _, hQ, he, -, hfin, -⟩ :=
    Algebra.exists_etale_isIdempotentElem_forall_liesOver_eq (Q.under A) Q
  let T := A' ⊗[A] B
  let D := Localization.Away e
  have hD : Module.Flat A' D := QuasiFiniteFibreFlat.flat_away H A' e
  let i : B →+* T := Algebra.TensorProduct.includeRight.toRingHom
  have hi : i.Flat := by
    have h1 : (algebraMap B (B ⊗[A] A')).Flat := RingHom.flat_algebraMap_iff.mpr inferInstance
    exact h1.comp (g := (Algebra.TensorProduct.comm A B A' : B ⊗[A] A' →+* A' ⊗[A] B))
          (.of_bijective (Algebra.TensorProduct.comm A B A').bijective)
  let β := Localization.localRingHom Q Q' i hQ.symm
  have hβ : β.Flat := RingHom.Flat.localRingHom hi Q' Q hQ.symm
  have hle : Submonoid.powers e ≤ Q'.primeCompl := by
    rw [Submonoid.powers_le]; exact he
  letI : Algebra D (Localization.AtPrime Q') :=
    IsLocalization.localizationAlgebraOfSubmonoidLe _ _ _ _ hle
  haveI : IsScalarTower T D (Localization.AtPrime Q') :=
    IsLocalization.localization_isScalarTower_of_submonoid_le _ _ _ _ hle
  haveI := IsLocalization.isLocalization_of_submonoid_le D (Localization.AtPrime Q') _ _ hle
  have hDQ : Module.Flat D (Localization.AtPrime Q') :=
    IsLocalization.flat _ (Q'.primeCompl.map (algebraMap T D))
  rw [← RingHom.flat_algebraMap_iff]
  refine ringHom_flat_of_square_of_isLocalHom (α := algebraMap A A') (β := β)
    (φ' := (algebraMap D (Localization.AtPrime Q')).comp (algebraMap A' D)) ?_
    (RingHom.flat_algebraMap_iff.mpr inferInstance) hβ
    ((RingHom.flat_algebraMap_iff.mpr hD).comp (RingHom.flat_algebraMap_iff.mpr hDQ))
  ext a
  simp only [RingHom.comp_apply]
  rw [IsScalarTower.algebraMap_apply A B (Localization.AtPrime Q), Localization.localRingHom_to_map,
    IsScalarTower.algebraMap_apply A' T D, ← IsScalarTower.algebraMap_apply T D]
  congr 1
  exact Algebra.TensorProduct.tmul_one_eq_one_tmul a
end GlobalTheory
