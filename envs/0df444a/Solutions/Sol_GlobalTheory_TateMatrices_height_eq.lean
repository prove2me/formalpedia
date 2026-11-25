-- Prove2me | solution 1 for GlobalTheory.TateMatrices.height_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:12:47.567807+00:00
-- url     : https://prove2.me/submissions/7e5605ea-3a89-42d4-b60c-5144b214b93f

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_CharR
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemSpan
import Definitions.Def_ReciprocityTheory_DualLattices_ThmAAll
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsTateMatricesLink
import Theorems.Thm_GlobalTheory_TateMatrices_map_eq_val
import Theorems.Thm_GlobalTheory_TateMatrices_tangent_eq
import Theorems.Thm_ReciprocityTheory_PGsh_ATower_char_R
import Theorems.Thm_ReciprocityTheory_PGsh_BX_isHeight_unique
import Theorems.Thm_ReciprocityTheory_PGsh_hext_tmul
import Theorems.Thm_ReciprocityTheory_PGsh_htLin
import Theorems.Thm_ReciprocityTheory_PGsh_linHt
import Theorems.Thm_ReciprocityTheory_PGsh_pairingProperties


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2
noncomputable section
open GlobalTheory
open GlobalTheory.TateMatrices
variable {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} (B : BX R₀)
namespace GlobalTheory.TateMatrices
theorem _root_.solution (Tw : ATower R₀ p) [Algebra ℤ_[p] (Tw.O : Type)] (Dp : ∀ n, DualPair (Tw.R n))
    (gb : Module.Basis (Fin g) R₀ B.gg) (A : OAdj B Tw.O) (M : Matrix (Fin g) (Fin g) (Tw.O : Type))
    (hM : ∀ {R S : LAlg R₀} (s : LHom Tw.O R) (π : LHom R S) (hπ : π.SqZero) (l : Fin g)
      (i : π.ker) (m : Fin g → π.ker), (∀ k, (m k : (R : Type)) = s.1 (M k l) * i) →
      A.ab.f s (B.tg π hπ (gb l ⊗ₜ[R₀] i)) = B.tg π hπ (∑ k, gb k ⊗ₜ[R₀] m k))
    {κ : Type} [Fintype κ] (τ : κ → ℕ → B.G Tw.O) (hτ : ∀ i n, (p ^ (n + 1)) • τ i n = 0)
    (ht : κ → B.gg →ₗ[R₀] (Tw.O : Type))
    (hht : ∀ i n, B.IsHeight (Dp n) (p ^ (n + 1)) (B.map (Tw.q n) (τ i n))
      ((Tw.q n).1.toLinearMap ∘ₗ ht i))
    (j : κ) (c : κ → ℤ_[p])
    (hc : ∀ n, A.a.f (LHom.id Tw.O) (τ j n) = ∑ k, (PadicInt.toZModPow (n + 1) (c k)).val • τ k n)
    (l : Fin g) :
    ∑ k, ht k (gb l) * algebraMap ℤ_[p] (Tw.O : Type) (c k) = ∑ k, M k l * ht j (gb k) := by
  rw [← sub_eq_zero]
  refine Tw.sep _ fun n => ?_
  have hchar := Tw.char_R n
  have hy : (p ^ (n + 1)) • B.map (Tw.q n) (τ j n) = 0 := by rw [← map_nsmul, hτ, map_zero]
  have H1 := linHt B Tw.O A (Tw.R n) (Tw.q n) (Dp n) _ _ _ _ hy (hht j n)
    (tangent_eq B gb A.ab M (Tw.q n) (Dp n) (fun l i m h => hM _ _ _ l i m h))
  have H2 := htLin B (pairingProperties B) Tw Dp κ τ ht
    (fun k n => ((PadicInt.toZModPow (n + 1) (c k)).val : ℤ))
    (fun k => algebraMap ℤ_[p] (Tw.O : Type) (c k)) hτ hht (fun k n => by
      have := map_eq_val (((Tw.q n).1 : (Tw.O : Type) →+* (Tw.R n : Type)).comp
        (algebraMap ℤ_[p] (Tw.O : Type))) (n + 1) (by exact_mod_cast Tw.char_R n) (c k)
      rw [Int.cast_natCast]
      exact this) n
  simp only [natCast_zsmul] at H2
  rw [← hc n, ← A.a.nat] at H2
  have hya : (p ^ (n + 1)) • A.a.f (Tw.q n) (B.map (Tw.q n) (τ j n)) = 0 := by
    rw [← map_nsmul, hy, map_zero]
  have H3 := B.isHeight_unique (pairingProperties B) (Dp n) _ hchar _ hya _ _ H1 H2
  have H4 := LinearMap.congr_fun H3 (gb l)
  simp only [LinearMap.comp_apply, Module.Basis.constr_basis, map_sum, hext_tmul,
    AlgHom.toLinearMap_apply, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    map_mul] at H4
  simp only [map_sub, map_sum, map_mul]
  rw [sub_eq_zero]
  simp only [mul_comm] at H4 ⊢
  exact H4.symm
end GlobalTheory.TateMatrices
