-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.SW.GoodTrans.good_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:36:30.424907+00:00
-- url     : https://prove2.me/submissions/a5326b6c-987c-4291-ae90-b0aac6a1809f

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_IntegralAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorIntegerRingAlmostAllPlaces
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GermConstantsEqAlongAffineSpaceSquare
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodTrans_transit_ring
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodTrans_mem_latV_iff
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodTrans_mulVec_mem
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodInt_rational_integral_units
import Theorems.Thm_GlobalTheory_CompanionTheory_SW_GoodRing_good_ring
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_LocalLattice_hermPairing_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_cc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_intCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_inv
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_natCast
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_neg
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_HermitianTraceFormVanishing_cc_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk
attribute [local simp] GlobalTheory.LocalLattice.hermPairing_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_add
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_cc
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_eq_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_intCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_inv
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_mul
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_natCast
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_neg
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_one
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_sub
attribute [local simp] ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.cc_zero



set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GoodTrans
namespace GlobalTheory.CompanionTheory.SW.GoodTrans
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (t : F), t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ x y : Fin 1 → Fin M → Fv F v ⊗[F] E, x ∈ latV b v → y ∈ latV b v → gramR (Fv F v) σ J x = (hermScal (Fv F v) σ (algebraMap F _ t) : HermR (Fv F v) σ 1) → gramR (Fv F v) σ J y = gramR (Fv F v) σ J x → ∃ h : HA (Fv F v) σ J, actW (Fv F v) σ J h x = y ∧ ∀ (n : ℕ) (X : Fin n → Fin M → Fv F v ⊗[F] E), actW (Fv F v) σ J h X ∈ latV b v ↔ X ∈ latV b v := by
  intro F E _ _ _ _ _ σ h M J hJ t ht d b
  have hinv : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    rw [h.2.2.2, h.2.2.2, star_star]
  have I := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ h d b
  filter_upwards [GlobalTheory.CompanionTheory.SW.GoodRing.good_ring F E σ h d b, I.2 t ht,
    Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => I.1 (J i j)] with v hring hv hJv
  obtain ⟨O, hO, hstab, -, -, -, hgood, -⟩ := hring
  intro x y hx hy hxt hyx
  have hss : ∀ z : Fv F v ⊗[F] E, sigR (Fv F v) σ (sigR (Fv F v) σ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      show a ⊗ₜ[F] σ (σ e) = a ⊗ₜ[F] e
      rw [hinv]
    | add p q hp hq => rw [map_add, map_add, hp, hq]
  have hc : ∀ c : Fv F v, c ∈ v.adicCompletionIntegers F → c ⊗ₜ[F] (1 : E) ∈ O := by
    intro c hcv
    refine (hO _).2 fun k => ?_
    have e : c ⊗ₜ[F] (1 : E) = c • (1 : Fv F v ⊗[F] E) := by
      rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
    exact mul_mem hcv ((hO 1).1 O.one_mem k)
  set c : Fv F v := algebraMap F (Fv F v) t with hcdef
  have hc0 : c ≠ 0 := fun h0 => by
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  have hβ : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) = c ⊗ₜ[F] (1 : E) :=
    congrFun (congrFun hxt 0) 0
  have hxy : hform (sigR (Fv F v) σ) (JR (Fv F v) J) (x 0) (x 0) =
      hform (sigR (Fv F v) σ) (JR (Fv F v) J) (y 0) (y 0) :=
    (congrFun (congrFun hyx 0) 0).symm
  have hci : c⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hv, inv_one]
  have hmul : c ⊗ₜ[F] (1 : E) * c⁻¹ ⊗ₜ[F] (1 : E) = 1 := by
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_inv_cancel₀ hc0, mul_one,
      Algebra.TensorProduct.one_def]
  obtain ⟨g, hg, hgx, hgO, hgiO⟩ := transit_ring O (sigR (Fv F v) σ) hstab hss (JR (Fv F v) J)
    (fun i j => (hO _).2 (hJv i j))
    (fun i j => by
      show sigR (Fv F v) σ (inclR (Fv F v) (J j i)) = inclR (Fv F v) (J i j)
      rw [← hJ.1 i j]
      rfl)
    (x 0) (y 0) (fun i => (hO _).2 (hx 0 i)) (fun i => (hO _).2 (hy 0 i)) hxy
    (c⁻¹ ⊗ₜ[F] (1 : E)) (hc _ hci) (by rw [hβ, hmul]) hgood
  let h' : HA (Fv F v) σ J := (⟨g, hg⟩ : HR (Fv F v) σ J)
  have hact : ∀ {n : ℕ} (X : Fin n → Fin M → Fv F v ⊗[F] E) (a : Fin n),
      actW (Fv F v) σ J h' X a = (g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a :=
    fun _ _ => rfl
  refine ⟨h', ?_, fun n X => ?_⟩
  · funext a
    rw [hact, Fin.fin_one_eq_zero a, hgx]
  · rw [mem_latV_iff b v O hO, mem_latV_iff b v O hO]
    constructor
    · intro hX a i
      have e : X a = ((g⁻¹ : GL (Fin M) (Fv F v ⊗[F] E)) : Matrix (Fin M) (Fin M) _) *ᵥ
          ((g : Matrix (Fin M) (Fin M) (Fv F v ⊗[F] E)) *ᵥ X a) := by
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
      rw [e]
      exact mulVec_mem O _ hgiO _ (fun j => by rw [← hact]; exact hX a j) i
    · intro hX a i
      rw [hact]
      exact mulVec_mem O _ hgO _ (hX a) i
end GlobalTheory.CompanionTheory.SW.GoodTrans
