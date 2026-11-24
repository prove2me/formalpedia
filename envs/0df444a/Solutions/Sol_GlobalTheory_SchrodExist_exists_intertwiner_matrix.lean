-- Prove2me | solution 1 for GlobalTheory.SchrodExist.exists_intertwiner_matrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:46.608908+00:00
-- url     : https://prove2.me/submissions/68c9a50f-14b3-46a1-9c24-33416ac6f8ac

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_LinearIndependentWave
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixIntegersModNatFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsNeZeroOfEventually
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsSchrodingerIntertwinerIntegralMatrices
import Theorems.Thm_GlobalTheory_SchrodExist_exists_intertwiner_span
import Theorems.Thm_GlobalTheory_SchrodExist_mem_intLat
import Theorems.Thm_GlobalTheory_SchrodExist_mem_annLat
import Theorems.Thm_GlobalTheory_SchrodExist_inv_nsmul_nsmul
import Theorems.Thm_GlobalTheory_SchrodExist_liftZ_of_eq
import Theorems.Thm_GlobalTheory_SchrodExist_liftZ_of_ne
import Theorems.Thm_GlobalTheory_SBUnif_sb_lattice_bounds
import Theorems.Thm_GlobalTheory_matrix_integers_mod_nat_finite


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel GlobalTheory.SplitWeil Matrix
noncomputable section
open GlobalTheory GlobalTheory.SchrodExist
open GlobalTheory.PlaceModel
namespace GlobalTheory.SchrodExist
theorem _root_.solution : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (Z : Type) [AddCommGroup Z] (χ : Matrix Y Y' k → Z → ℂ), (∀ a b z, χ (a + b) z = χ a z * χ b z) → (∀ a z z', χ a (z + z') = χ a z * χ a z') → (∀ z, χ 0 z = 1) → (∀ a, χ a 0 = 1) → (∀ n : ℕ, 0 < n → ∀ z : Z, ∃ z' : Z, n • z' = z) → (∀ n : ℕ, 0 < n → Function.Injective fun z : Z => n • z) → (∀ x : Matrix Y Y' k, (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → χ x z = 1) → ∀ r q, x r q ∈ 𝒪[k]) → ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (τ : Matrix Y Y' k → M →ₗ[ℂ] M) (μ : Z → M →ₗ[ℂ] M), (∀ x x' f, τ x (τ x' f) = τ (x + x') f) → (∀ z z' f, μ z (μ z' f) = μ (z + z') f) → (∀ x z f, τ x (μ z f) = χ x z • μ z (τ x f)) → (∀ f, τ 0 f = f) → (∀ f, μ 0 f = f) → ∀ f₀ : M, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → τ u f₀ = f₀) → (∀ z, (∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u z = 1) → μ z f₀ = f₀) → ∃ Tm : SB (Matrix Y Y' k) →ₗ[ℂ] M, (∀ (x : Matrix Y Y' k) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = Φ.1 (t + x)) → Tm Φ' = τ x (Tm Φ)) ∧ (∀ (z : Z) (Φ Φ' : SB (Matrix Y Y' k)), (∀ t, Φ'.1 t = χ t z * Φ.1 t) → Tm Φ' = μ z (Tm Φ)) ∧ (∀ Φ : SB (Matrix Y Y' k), Φ.1 = Set.indicator {x | ∀ r q, x r q ∈ 𝒪[k]} (fun _ => 1) → Tm Φ = f₀) ∧ ∀ Φ, Tm Φ ∈ Submodule.span ℂ (Set.range fun w : Matrix Y Y' k × Z => τ w.1 (μ w.2 f₀)) := by
  intro k _ _ _ _ _ Y Y' _ _ _ _ Z _ χ hl hr hz0 ha0 hdiv hinj hann M _ _ τ μ hτ hμ hτμ hτ0 hμ0 f₀ hfτ hfμ
  classical
  let χG : Matrix Y Y' k × Z → Matrix Y Y' k × Z → ℂ := fun g h => χ g.1 h.2
  have hB : IsBichar χG :=
    ⟨fun a b y => hl a.1 b.1 y.2, fun a y z => hr a.1 y.2 z.2, fun y => hz0 y.2, fun a => ha0 a.1⟩
  let SX : AddSubgroup (Matrix Y Y' k × Z) := (⊤ : AddSubgroup (Matrix Y Y' k)).prod ⊥
  let SY : AddSubgroup (Matrix Y Y' k × Z) := (⊥ : AddSubgroup (Matrix Y Y' k)).prod ⊤
  let SL : AddSubgroup (Matrix Y Y' k × Z) := (intLat k Y Y').prod ⊥
  let SL' : AddSubgroup (Matrix Y Y' k × Z) := (⊥ : AddSubgroup (Matrix Y Y' k)).prod (annLat χ hr ha0)
  have mX : ∀ g, g ∈ SX ↔ g.2 = 0 := fun g => by simp [SX, AddSubgroup.mem_prod]
  have mY : ∀ g, g ∈ SY ↔ g.1 = 0 := fun g => by simp [SY, AddSubgroup.mem_prod]
  have mL : ∀ g, g ∈ SL ↔ (∀ r q, g.1 r q ∈ 𝒪[k]) ∧ g.2 = 0 := fun g => by
    simp [SL, AddSubgroup.mem_prod, mem_intLat]
  have mL' : ∀ g, g ∈ SL' ↔ g.1 = 0 ∧ ∀ u : Matrix Y Y' k, (∀ r q, u r q ∈ 𝒪[k]) → χ u g.2 = 1 := fun g => by
    simp [SL', AddSubgroup.mem_prod, mem_annLat]
  let ρ : Matrix Y Y' k × Z → M →ₗ[ℂ] M := fun g => (τ g.1).comp (μ g.2)
  have hρ : ∀ g f, ρ g f = τ g.1 (μ g.2 f) := fun _ _ => rfl
  have hL : SL ≤ SX := fun g hg => (mX g).2 ((mL g).1 hg).2
  have hL' : SL' ≤ SY := fun g hg => (mY g).2 ((mL' g).1 hg).1
  have hLL' : ∀ u ∈ SL, ∀ y ∈ SL', χG u y = 1 := fun u hu y hy => ((mL' y).1 hy).2 u.1 ((mL u).1 hu).1
  have hX : ∀ x ∈ SX, (∀ y ∈ SL', χG x y = 1) → x ∈ SL := by
    intro x hx h
    refine (mL x).2 ⟨hann x.1 fun z hz => ?_, (mX x).1 hx⟩
    exact h (0, z) ((mL' _).2 ⟨rfl, hz⟩)
  have hY : ∀ y ∈ SY, (∀ u ∈ SL, χG u y = 1) → y ∈ SL' := by
    intro y hy h
    exact (mL' y).2 ⟨(mY y).1 hy, fun u hu => h (u, 0) ((mL _).2 ⟨hu, rfl⟩)⟩
  have dX : ∀ n : ℕ, 0 < n → ∀ x ∈ SX, ∃ x' ∈ SX, n • x' = x := by
    intro n hn x hx
    refine ⟨((n : k)⁻¹ • x.1, 0), (mX _).2 rfl, Prod.ext ?_ ?_⟩
    · show n • ((n : k)⁻¹ • x.1) = x.1
      rw [← Nat.cast_smul_eq_nsmul k, smul_smul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hn.ne'), one_smul]
    · show n • (0 : Z) = x.2
      rw [smul_zero, (mX x).1 hx]
  have dY : ∀ n : ℕ, 0 < n → ∀ y ∈ SY, ∃ y' ∈ SY, n • y' = y := by
    intro n hn y hy
    obtain ⟨z', hz'⟩ := hdiv n hn y.2
    refine ⟨(0, z'), (mY _).2 rfl, Prod.ext ?_ ?_⟩
    · show n • (0 : Matrix Y Y' k) = y.1
      rw [smul_zero, (mY y).1 hy]
    · exact hz'
  have tf : ∀ n : ℕ, 0 < n → Function.Injective fun t : Matrix Y Y' k × Z => n • t := by
    intro n hn a b hab
    have h1 : n • a.1 = n • b.1 := congrArg Prod.fst hab
    have h2 : n • a.2 = n • b.2 := congrArg Prod.snd hab
    refine Prod.ext ?_ (hinj n hn h2)
    have h3 := congrArg (fun m => (n : k)⁻¹ • m) h1
    simpa only [inv_nsmul_nsmul n hn] using h3
  have hfin : ∀ n : ℕ, 0 < n → ∃ R : Set (Matrix Y Y' k × Z), R.Finite ∧
      ∀ t ∈ SL, ∃ r ∈ R, ∃ u ∈ SL, t = r + n • u := by
    intro n hn
    obtain ⟨R, hR, hRt⟩ := GlobalTheory.matrix_integers_mod_nat_finite k Y Y' n hn
    refine ⟨(fun m => (m, (0 : Z))) '' R, hR.image _, ?_⟩
    intro t ht
    obtain ⟨hint, h2⟩ := (mL t).1 ht
    obtain ⟨s, hs, u, hu, hst⟩ := hRt t.1 hint
    refine ⟨(s, 0), ⟨s, hs, rfl⟩, (u, 0), (mL _).2 ⟨hu, rfl⟩, Prod.ext hst ?_⟩
    show t.2 = 0 + n • (0 : Z)
    rw [h2, smul_zero, add_zero]
  have ρX : ∀ x ∈ SX, ∀ x' ∈ SX, ∀ f, ρ x (ρ x' f) = ρ (x + x') f := by
    intro x hx x' hx' f
    have hs : (x + x').2 = 0 := by
      show x.2 + x'.2 = 0
      rw [(mX x).1 hx, (mX x').1 hx', add_zero]
    rw [hρ, hρ, hρ, hs, (mX x).1 hx, (mX x').1 hx']
    simp only [hμ0]
    exact hτ _ _ _
  have ρY : ∀ y ∈ SY, ∀ y' ∈ SY, ∀ f, ρ y (ρ y' f) = ρ (y + y') f := by
    intro y hy y' hy' f
    have hs : (y + y').1 = 0 := by
      show y.1 + y'.1 = 0
      rw [(mY y).1 hy, (mY y').1 hy', add_zero]
    rw [hρ, hρ, hρ, hs, (mY y).1 hy, (mY y').1 hy']
    simp only [hτ0]
    exact hμ _ _ _
  have ρXY : ∀ x ∈ SX, ∀ y ∈ SY, ∀ f, ρ x (ρ y f) = χG x y • ρ y (ρ x f) := by
    intro x hx y hy f
    rw [hρ, hρ, hρ, hρ, (mX x).1 hx, (mY y).1 hy]
    simp only [hμ0, hτ0]
    exact hτμ x.1 y.2 f
  have hf : ∀ u ∈ SL, ρ u f₀ = f₀ := by
    intro u hu
    obtain ⟨hint, h2⟩ := (mL u).1 hu
    rw [hρ, h2, hμ0]
    exact hfτ u.1 hint
  have hf' : ∀ u ∈ SL', ρ u f₀ = f₀ := by
    intro u hu
    obtain ⟨h1, hz⟩ := (mL' u).1 hu
    rw [hρ, h1, hτ0]
    exact hfμ u.2 hz
  obtain ⟨T, hT0, hT⟩ := exists_intertwiner_span hB hL hL' hLL' hX hY dX dY tf hfin ρ ρX ρY ρXY f₀ hf hf'
  have good : ∀ Φ : SB (Matrix Y Y' k), ∃ n : ℕ, 0 < n ∧
      (∀ u ∈ SL, ∀ t, (liftZ Φ : Matrix Y Y' k × Z → ℂ) (t + n • u) = liftZ Φ t) ∧
      (∀ t, (liftZ Φ : Matrix Y Y' k × Z → ℂ) t ≠ 0 → n • t ∈ SL) := by
    intro Φ
    obtain ⟨n, hn, hinv, hsupp⟩ := GlobalTheory.SBUnif.sb_lattice_bounds k Y Y' Φ.1 Φ.2
    refine ⟨n, hn, fun u hu t => ?_, fun t ht => ?_⟩
    · obtain ⟨hint, h2⟩ := (mL u).1 hu
      by_cases ht : t.2 = 0
      · have ht' : (t + n • u).2 = 0 := by
          show t.2 + n • u.2 = 0
          rw [ht, h2, smul_zero, add_zero]
        rw [liftZ_of_eq Φ ht', liftZ_of_eq Φ ht]
        exact hinv u.1 hint t.1
      · have ht' : (t + n • u).2 ≠ 0 := by
          show t.2 + n • u.2 ≠ 0
          rw [h2, smul_zero, add_zero]
          exact ht
        rw [liftZ_of_ne Φ ht', liftZ_of_ne Φ ht]
    · by_cases h2 : t.2 = 0
      · rw [liftZ_of_eq Φ h2] at ht
        refine (mL _).2 ⟨hsupp t.1 ht, ?_⟩
        show n • t.2 = 0
        rw [h2, smul_zero]
      · exact absurd (liftZ_of_ne Φ h2) ht
  have supp : ∀ Φ : SB (Matrix Y Y' k), ∀ t, (liftZ Φ : Matrix Y Y' k × Z → ℂ) t ≠ 0 → t ∈ SX :=
    fun Φ t ht => (mX t).2 (by_contra fun h => ht (liftZ_of_ne Φ h))
  have app : ∀ Φ : SB (Matrix Y Y' k),
      (∀ x ∈ SX, T (fun t => liftZ Φ (t + x)) = ρ x (T (liftZ Φ))) ∧
      (∀ y ∈ SY, T (fun t => χG t y * liftZ Φ t) = ρ y (T (liftZ Φ))) ∧
      T (liftZ Φ) ∈ Submodule.span ℂ {v | ∃ x ∈ SX, ∃ y ∈ SY, v = ρ x (ρ y f₀)} := by
    intro Φ
    obtain ⟨n, hn, h1, h2⟩ := good Φ
    exact hT (liftZ Φ) (supp Φ) n hn h1 h2
  refine ⟨T.comp liftZ, ?_, ?_, ?_, ?_⟩
  · intro x Φ Φ' hΦ'
    have e : (liftZ Φ' : Matrix Y Y' k × Z → ℂ) = fun t => liftZ Φ (t + (x, 0)) := by
      funext t
      by_cases h2 : t.2 = 0
      · have h2' : (t + (x, (0 : Z))).2 = 0 := by
          show t.2 + 0 = 0
          rw [h2, add_zero]
        rw [liftZ_of_eq Φ' h2, liftZ_of_eq Φ h2']
        exact hΦ' t.1
      · have h2' : (t + (x, (0 : Z))).2 ≠ 0 := by
          show t.2 + 0 ≠ 0
          rw [add_zero]
          exact h2
        rw [liftZ_of_ne Φ' h2, liftZ_of_ne Φ h2']
    show T (liftZ Φ') = τ x (T (liftZ Φ))
    rw [e, (app Φ).1 (x, 0) ((mX _).2 rfl), hρ]
    exact congrArg (τ x) (hμ0 _)
  · intro z Φ Φ' hΦ'
    have e : (liftZ Φ' : Matrix Y Y' k × Z → ℂ) = fun t => χG t (0, z) * liftZ Φ t := by
      funext t
      by_cases h2 : t.2 = 0
      · rw [liftZ_of_eq Φ' h2, liftZ_of_eq Φ h2]
        exact hΦ' t.1
      · rw [liftZ_of_ne Φ' h2, liftZ_of_ne Φ h2, mul_zero]
    show T (liftZ Φ') = μ z (T (liftZ Φ))
    rw [e, (app Φ).2.1 (0, z) ((mY _).2 rfl), hρ]
    exact hτ0 _
  · intro Φ hΦ
    have e : (liftZ Φ : Matrix Y Y' k × Z → ℂ) = ind SL := by
      funext t
      by_cases h2 : t.2 = 0
      · rw [liftZ_of_eq Φ h2, hΦ]
        by_cases hi : ∀ r q, t.1 r q ∈ 𝒪[k]
        · have hm : t ∈ SL := (mL t).2 ⟨hi, h2⟩
          simp [ind, Set.indicator, hi, hm]
        · have hm : t ∉ SL := fun h => hi ((mL t).1 h).1
          simp [ind, Set.indicator, hi, hm]
      · rw [liftZ_of_ne Φ h2]
        have hm : t ∉ SL := fun h => h2 ((mL t).1 h).2
        simp [ind, hm]
    show T (liftZ Φ) = f₀
    rw [e, hT0]
  · intro Φ
    refine Submodule.span_mono ?_ (app Φ).2.2
    rintro v ⟨x, hx, y, hy, rfl⟩
    refine ⟨(x.1, y.2), ?_⟩
    show τ x.1 (μ y.2 f₀) = ρ x (ρ y f₀)
    rw [hρ, hρ, (mX x).1 hx, (mY y).1 hy]
    simp only [hμ0, hτ0]
end GlobalTheory.SchrodExist
