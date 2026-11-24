-- Prove2me | solution 1 for GlobalTheory.UTrans.exists_isU_conj_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:57:33.298806+00:00
-- url     : https://prove2.me/submissions/8710c482-03d6-4503-9574-0a3fd68dc9da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidAdjustIntegralAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryEqQuasiReflectionMulTransvections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryTransvectionSubmonoidNormalDetOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TransvectionIdentitiesUnitary
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsUnitaryConjSplitLatticeOfLocal
import Theorems.Thm_GlobalTheory_UTrans_mem_of_coprime_nsmul
import Theorems.Thm_GlobalTheory_UTrans_awayLoc_of_nsmul
import Theorems.Thm_GlobalTheory_UTrans_le_awayLoc
import Theorems.Thm_GlobalTheory_UTrans_awayLoc_map
import Theorems.Thm_GlobalTheory_UTrans_Calc_calculus
import Theorems.Thm_GlobalTheory_UTrans_isU_eq_tv_mul_tvGen
import Theorems.Thm_GlobalTheory_UTrans_tvGen_adjust
import Theorems.Thm_GlobalTheory_UTrans_tvGen_normal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory GlobalTheory.UTrans
namespace GlobalTheory.UTrans
theorem _root_.solution : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (c : E ≃ₐ[F] E) (n : ℕ) (G : Matrix (Fin n) (Fin n) E), Module.finrank F E = 2 → GlobalTheory.UTrans.IsHerm (c : E →+* E) G → (∃ z : Fin n → E, z ≠ 0 ∧ GlobalTheory.UTrans.hf (c : E →+* E) G z z = 0) → ∀ L L₀ : Submodule (𝓞 E) (Fin n → E), L.FG → Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (π γ₀ : Matrix (Fin n) (Fin n) E) (x : Fin n → E) (b k : ℕ), π * π = π → (∀ v w, GlobalTheory.UTrans.hf (c : E →+* E) G (π.mulVec v) w = GlobalTheory.UTrans.hf (c : E →+* E) G v (π.mulVec w)) → π.mulVec x = x → GlobalTheory.UTrans.hf (c : E →+* E) G x x ≠ 0 → (∀ v ∈ L₀, π.mulVec v ∈ L₀) → 0 < b → (∀ v ∈ L, b • v ∈ L₀) → (∀ v ∈ L₀, b • v ∈ L) → GlobalTheory.UTrans.IsU (c : E →+* E) G γ₀ → k.Coprime b → (∀ v ∈ L, k • γ₀.mulVec v ∈ L₀) → (∀ v ∈ L₀, k • γ₀⁻¹.mulVec v ∈ L) → ∃ γ : Matrix (Fin n) (Fin n) E, GlobalTheory.UTrans.IsU (c : E →+* E) G γ ∧ ∀ v ∈ L, (γ⁻¹ * π * γ).mulVec v ∈ L := by
  intro F E _ _ _ _ _ c n G hFE hG hz L L₀ hL hsp π γ₀ x b k _ hsa hx hxx hπ hb hb1 hb2 hγ hk hk1 hk2
  obtain ⟨m, hm, hγm⟩ := (GlobalTheory.UTrans.isU_eq_tv_mul_tvGen F E c n G hG hz γ₀ hγ).1 x hxx
  obtain ⟨hN1, hN2⟩ := GlobalTheory.UTrans.tvGen_normal E n (c : E →+* E) G hG
  have hC := GlobalTheory.UTrans.Calc.calculus E n (c : E →+* E) G hG.invol hG.herm
  set s := tv (c : E →+* E) G x ((γ₀.det - 1) / hf (c : E →+* E) G x x) with hs
  have hsπ : s * π = π * s := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    simp only [Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hs, hC.2.1, Matrix.mulVec_add, Matrix.mulVec_smul,
      hsa, hx]
  have hγd : IsUnit γ₀.det := by
    refine IsUnit.mk0 _ fun h => ?_
    have := (hN1 γ₀ hγ).1
    simp [h] at this
  obtain ⟨-, hmd, hmi, -⟩ := hN2 m hm
  have hmu : IsUnit m.det := by simp [hmd]
  have hsu : IsUnit s.det := by
    rw [hγm, Matrix.det_mul, hmd, mul_one] at hγd
    exact hγd
  have hP : γ₀⁻¹ * π * γ₀ = m⁻¹ * π * m := by
    rw [hγm, Matrix.mul_inv_rev]
    calc m⁻¹ * s⁻¹ * π * (s * m) = m⁻¹ * (s⁻¹ * (π * s)) * m := by simp only [Matrix.mul_assoc]
      _ = m⁻¹ * π * m := by rw [← hsπ, Matrix.nonsing_inv_mul_cancel_left _ _ hsu]
  set A := L.toAddSubgroup with hA
  have hPL : ∀ v ∈ awayLoc A b, (m⁻¹ * π * m) *ᵥ v ∈ awayLoc A b := by
    refine awayLoc_map A b _ (fun K v => Matrix.mulVec_smul _ _ _) fun v hv => ⟨k * k, Nat.Coprime.mul_left hk hk, ?_⟩
    have := hk2 _ (hπ _ (hk1 v hv))
    rw [Matrix.mulVec_smul, Matrix.mulVec_smul, smul_smul, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hP] at this
    exact this
  have hden : ∀ p ∈ TvGen (c : E →+* E) G, ∃ e : ℕ, ∀ v ∈ awayLoc A b, b ^ e • (p *ᵥ v) ∈ awayLoc A b := by
    intro p hp
    obtain ⟨q, -, k₀, e₀, hk₀, H₀⟩ := tvGen_adjust F E c n G hFE hG L hL hsp p hp b hb 0
    refine ⟨e₀, awayLoc_map A b _ (fun K v => by rw [Matrix.mulVec_smul, smul_comm]) fun v hv => ⟨k₀, hk₀, ?_⟩⟩
    obtain ⟨⟨w, hw, h1⟩, h2, -⟩ := H₀ v hv
    have : k₀ • b ^ e₀ • (p *ᵥ v) = k₀ • b ^ e₀ • (q *ᵥ v) - b ^ e₀ • (b ^ 0 • w) := by
      rw [← h1]; module
    rw [this]
    exact sub_mem (nsmul_mem h2 _) (nsmul_mem (nsmul_mem hw _) _)
  obtain ⟨e₁, he₁⟩ := hden _ hmi
  obtain ⟨q, hq, k', e, hk', H⟩ := tvGen_adjust F E c n G hFE hG L hL hsp m hm b hb (e₁ + 1)
  obtain ⟨hqU, hqd, hqi, -⟩ := hN2 q hq
  have hqu : IsUnit q.det := by simp [hqd]
  have hbE : (b : E) ≠ 0 := Nat.cast_ne_zero.2 hb.ne'

  have hδ : ∀ v ∈ awayLoc A b, ∃ w ∈ awayLoc A b, (m⁻¹ * q) *ᵥ v = v + b • w := by
    have h1 : ∀ v ∈ awayLoc A b, (b : E)⁻¹ • ((m⁻¹ * q) *ᵥ v - v) ∈ awayLoc A b := by
      refine awayLoc_map A b _ (fun K v => by rw [Matrix.mulVec_smul, ← smul_sub, smul_comm]) fun v hv => ?_
      obtain ⟨⟨w, hw, h1⟩, -⟩ := H v hv
      apply awayLoc_of_nsmul A hk'
      have h2 := congrArg (fun u => m⁻¹ *ᵥ u) h1
      simp only [Matrix.mulVec_smul, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hmu,
        Matrix.one_mulVec] at h2
      rw [smul_comm, h2, pow_succ', mul_smul, ← Nat.cast_smul_eq_nsmul E b, smul_smul, inv_mul_cancel₀ hbE, one_smul]
      exact he₁ _ (le_awayLoc A b hw)
    intro v hv
    refine ⟨_, h1 v hv, ?_⟩
    rw [← Nat.cast_smul_eq_nsmul E b, smul_smul, mul_inv_cancel₀ hbE, one_smul]
    abel
  have hu : ∀ v ∈ awayLoc A b, (q⁻¹ * m) *ᵥ v ∈ awayLoc A b := by
    obtain ⟨r, hr⟩ := hden _ (mul_mem hqi hm)
    induction r with
    | zero => simpa using hr
    | succ r ih =>
      refine ih fun v hv => ?_
      obtain ⟨w, hw, h1⟩ := hδ v hv
      have h2 := congrArg (fun u => (q⁻¹ * m) *ᵥ u) h1
      have h3 : q⁻¹ * m * (m⁻¹ * q) = 1 := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hmu, Matrix.nonsing_inv_mul _ hqu]
      simp only [Matrix.mulVec_mulVec, h3, Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul] at h2
      have h4 : b ^ r • ((q⁻¹ * m) *ᵥ v) = b ^ r • v - b ^ (r + 1) • ((q⁻¹ * m) *ᵥ w) := by
        rw [eq_sub_iff_add_eq, pow_succ, mul_smul, ← smul_add, ← h2]
      rw [h4]
      exact sub_mem (nsmul_mem hv _) (hr w hw)
  refine ⟨q, hqU, fun v hv => ?_⟩
  have hQ : q⁻¹ * π * q = (q⁻¹ * m) * ((m⁻¹ * π * m) * (m⁻¹ * q)) := by
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hmu]
  have h1 : (q⁻¹ * π * q) *ᵥ v ∈ awayLoc A b := by
    rw [hQ, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec v (m⁻¹ * π * m)]
    apply hu
    apply hPL
    obtain ⟨w, hw, h⟩ := hδ v (le_awayLoc A b hv)
    rw [h]
    exact add_mem (le_awayLoc A b hv) (nsmul_mem hw _)
  obtain ⟨K, hK, h1⟩ := h1
  have h2 := (H _ (hb2 _ (hπ _ (hb1 _ (H v hv).2.1)))).2.2
  simp only [Matrix.mulVec_smul, Matrix.mulVec_mulVec, smul_smul, ← Matrix.mul_assoc] at h2
  refine mem_of_coprime_nsmul A ?_ h1 h2
  repeat' apply Nat.Coprime.mul_right
  all_goals first | exact hK | exact hK.pow_right _
end GlobalTheory.UTrans
