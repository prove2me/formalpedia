-- Prove2me | solution 1 for GlobalTheory.AbCoh.nonempty_model_of_quasiIso
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:53:06.778733+00:00
-- url     : https://prove2.me/submissions/682f7f67-87b3-4f45-baa5-6075a189dc15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsFiniteProjectiveComplexQuasiIso
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NonemptyStructureSheafCohomologyModelOfQuasiIso
import Theorems.Thm_GlobalTheory_AbCoh_coneExact_baseChange_of_quasiIso
import Theorems.Thm_GlobalTheory_AbCoh_cycMap_val
import Theorems.Thm_GlobalTheory_AbCoh_ext_comm
import Theorems.Thm_GlobalTheory_AbCoh_exact_comp
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_zero
import Theorems.Thm_GlobalTheory_CechDR_IsPull2_zero
import Theorems.Thm_GlobalTheory_CechDR_SemiHom_comp
import Theorems.Thm_GlobalTheory_CechDR_cechDeRhamTotalCocyclesTwo_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbCoh
namespace GlobalTheory.AbCoh
theorem _root_.solution : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R)
    (K C : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ C), (∀ (S : Type) [CommRing S] [Algebra R S],
      QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R S)).mapHomologicalComplex _).map φ)) →
    Model s C → Nonempty (Model s K) := by
  intro R _ X s K C φ hq M
  have h0 : IsPullback (𝟙 X) s s (spMap (algebraMap R R)) := by
    show IsPullback (𝟙 X) s s (spMap (RingHom.id R))
    rw [Cris.spMap_id]; exact IsPullback.id_horiz s
  obtain ⟨e1, -⟩ := M.θ0_one h0
  obtain ⟨y, hy1, hy2⟩ := (coneExact_baseChange_of_quasiIso φ (hq R)).zero ((1 : R) ⊗ₜ[R] M.one) 0
    ((LinearMap.mem_ker.1 e1).trans (map_zero _).symm) (map_zero _)
  let oneK : K.X 0 := TensorProduct.lid R (K.X 0) y
  have hy : (1 : R) ⊗ₜ[R] oneK = y := by
    rw [← TensorProduct.lid_symm_apply, LinearEquiv.symm_apply_apply]
  have hinj : ∀ {M : ModuleCat.{0} R} (a b : M), (1 : R) ⊗ₜ[R] a = (1 : R) ⊗ₜ[R] b → a = b := fun a b hab => by
    rw [← TensorProduct.lid_symm_apply, ← TensorProduct.lid_symm_apply] at hab
    exact (TensorProduct.lid R _).symm.injective hab
  have hφone : (φ.f 0).hom oneK = M.one := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy]; exact hy1)
  have hdone : (K.d 0 1).hom oneK = 0 := hinj _ _ (by
    rw [← LinearMap.baseChange_tmul, hy, TensorProduct.tmul_zero]; exact hy2)
  refine ⟨{
    θ0 := fun {R'} _ _ {X'} {s'} {ψ} h => (LinearEquiv.ofBijective (cycMap φ R' 0 1) ⟨?_, ?_⟩).trans (M.θ0 h)
    one := oneK
    θ0_one := ?_
    θ1 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ1 h).comp (cycMap φ R' 1 2)
    θ2 := fun {R'} _ _ {X'} {s'} {ψ} h => (M.θ2 h).comp (cycMap φ R' 2 3)
    exact := ?_
    nat := ?_ }⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact Subtype.ext ((coneExact_baseChange_of_quasiIso φ (hq _)).inj z.1 (congrArg Subtype.val hz) z.2)
  · intro w
    obtain ⟨x, hx1, hx2⟩ := (coneExact_baseChange_of_quasiIso φ (hq _)).zero w.1 0
      ((LinearMap.mem_ker.1 w.2).trans (map_zero _).symm) (map_zero _)
    exact ⟨⟨x, hx2⟩, Subtype.ext hx1⟩
  · intro R' _ _ X' s' ψ h
    have e : (1 : R') ⊗ₜ[R] oneK ∈ LinearMap.ker (dB K R' 0 1) := by
      rw [LinearMap.mem_ker, dB, LinearMap.baseChange_tmul, hdone, TensorProduct.tmul_zero]
    obtain ⟨e', he'⟩ := M.θ0_one h
    refine ⟨e, fun T => ?_⟩
    have hc : cycMap φ R' 0 1 ⟨_, e⟩ = ⟨_, e'⟩ := Subtype.ext (by
      rw [cycMap_val, LinearMap.baseChange_tmul, hφone])
    show (M.θ0 h (cycMap φ R' 0 1 ⟨_, e⟩)).1 T = 1
    rw [hc]; exact he' T
  · intro R' _ _ X' s' ψ h
    have hc := coneExact_baseChange_of_quasiIso φ (hq R')
    obtain ⟨s1, k1, s2, k2⟩ := M.exact h
    have A := exact_comp φ R' 0 1 2 (M.θ1 h) s1 k1
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 0 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨x, -, hx⟩ := hc.zero c k' hkc.symm hk'
        exact ⟨x, hx⟩)
    have B := exact_comp φ R' 1 2 3 (M.θ2 h) s2 k2
      (fun c hc0 => by
        obtain ⟨c', k', h1, h2⟩ := hc.succ 1 c 0 (hc0.trans (map_zero _).symm) (map_zero _)
        exact ⟨c', k', h2, h1⟩)
      (fun k' c hk' hkc => by
        obtain ⟨c', k'', -, hx⟩ := hc.succ 0 c k' hkc.symm hk'
        exact ⟨k'', hx⟩)
    exact ⟨A.1, A.2, B.1, B.2⟩
  · intro R' _ _ X' s' ψ h R'' _ _ X'' s'' ψ' h' α χ w hχ
    obtain ⟨n1, n2⟩ := M.nat h h' α χ w hχ
    refine ⟨fun z z' hz => ?_, fun z z' hz => ?_⟩
    · show M.θ1 h' (cycMap φ R'' 1 2 z') = pullHO1 w (M.θ1 h (cycMap φ R' 1 2 z))
      exact n1 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])
    · show M.θ2 h' (cycMap φ R'' 2 3 z') = pullHO2 w (M.θ2 h (cycMap φ R' 2 3 z))
      exact n2 _ _ (by rw [cycMap_val, cycMap_val, hz, ext_comm])
end GlobalTheory.AbCoh
