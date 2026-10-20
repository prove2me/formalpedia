-- Prove2me | solution 1 for OAI.Cotype.geometric_block_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T21:18:28.835562+00:00
-- url     : https://prove2.me/submissions/561e715b-558a-487f-8685-7a5724ffe83b

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ProjectionGenerator
import Definitions.Def_OAI_Analysis_Cotype_PowerGapInverse
import Definitions.Def_OAI_Analysis_Cotype_ExponentialIntegral
import Definitions.Def_OAI_Analysis_Cotype_ProjectionResolvent
import Definitions.Def_OAI_Analysis_Cotype_SectorResolvent
import Definitions.Def_OAI_Analysis_Cotype_FiniteContour
import Definitions.Def_OAI_Analysis_Cotype_NoiseHypercontractivity
import Definitions.Def_OAI_Analysis_Cotype_QuadraticTypeTensor
import Definitions.Def_OAI_Analysis_Cotype_WalshAmplification
import Definitions.Def_OAI_Analysis_Cotype_FiniteL2Dual
import Definitions.Def_OAI_Analysis_Cotype_DualMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_FiniteSupDual
import Definitions.Def_OAI_Analysis_Cotype_PrimalMomentLifts
import Definitions.Def_OAI_Analysis_Cotype_CotypeAmplification
import Definitions.Def_OAI_Analysis_Cotype_TypeCotypeDuality

open OAI OAI.Cotype
open scoped BigOperators
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
theorem h50d_sum_comp_emb {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ↪ κ)
    (g : (ι → Bool) → ℝ) :
    ∑ ε : κ → Bool, g (fun i => ε (e i)) =
      (Fintype.card ({k // k ∉ Set.range e} → Bool) : ℝ) * ∑ δ, g δ := by
  classical
  let E1 := Equiv.piEquivPiSubtypeProd (fun k => k ∈ Set.range e) (fun _ => Bool)
  rw [← E1.symm.sum_comp, Fintype.sum_prod_type]
  have h : ∀ a b, (fun i => E1.symm (a, b) (e i)) = fun i => a ⟨e i, ⟨i, rfl⟩⟩ := by
    intro a b; funext i
    simp [E1, Equiv.piEquivPiSubtypeProd]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  refine congrArg (fun t => _ * t) ?_
  let φ := Equiv.ofInjective e e.injective
  exact Fintype.sum_equiv (Equiv.arrowCongr φ.symm (Equiv.refl Bool))
    (fun a => g (fun i => a ⟨e i, ⟨i, rfl⟩⟩)) g (fun a => rfl)

theorem h50d_avg_comp_emb {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (e : ι ↪ κ)
    (g : (ι → Bool) → ℝ) :
    average (fun ε : κ → Bool => g (fun i => ε (e i))) = average g := by
  have h1 := h50d_sum_comp_emb e g
  have h2 := h50d_sum_comp_emb e (fun _ => 1)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one] at h2
  unfold average
  simp only [smul_eq_mul]
  rw [h1, h2]
  have hc1 : (Fintype.card ({k // k ∉ Set.range e} → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hc2 : (Fintype.card (ι → Bool) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp

theorem h50d_sum_emb {c N : ℕ} {M : Type*} [AddCommMonoid M] (e : Fin c ↪ Fin N)
    {Y : Type*} [Zero Y] (w : Fin N → Y) (z : Fin c → Y)
    (hw : ∀ j, w (e j) = z j) (h0 : ∀ k, k ∉ Set.range e → w k = 0)
    (F : Fin N → Y → M) (hF : ∀ k, F k 0 = 0) :
    ∑ k, F k (w k) = ∑ j, F (e j) (z j) := by
  classical
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.map e))]
  · rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hw]
  · intro k _ hk
    have : k ∉ Set.range e := by
      rintro ⟨i, rfl⟩; exact hk (Finset.mem_map_of_mem _ (Finset.mem_univ i))
    rw [h0 k this, hF]

theorem h50d_cubeL2_emb {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c N : ℕ} (e : Fin c ↪ Fin N) (w : Fin N → X) (z : Fin c → X)
    (hw : ∀ j, w (e j) = z j) (h0 : ∀ k, k ∉ Set.range e → w k = 0) :
    cubeL2 X (rademacherSum X w) = cubeL2 X (rademacherSum X z) := by
  unfold cubeL2
  congr 1
  have : ∀ ε : Cube N, rademacherSum X w ε = rademacherSum X z (fun i => ε (e i)) := by
    intro ε
    unfold rademacherSum
    exact h50d_sum_emb e w z hw h0 (fun k v => sign (ε k) • v) (fun k => smul_zero _)
  simp only [this]
  exact h50d_avg_comp_emb e (fun δ => ‖rademacherSum X z δ‖ ^ 2)

theorem solution {N n k : ℕ} {A r : ℝ} (hA : 0 ≤ A) (hr : 0 < r)
    (h : QuadraticTypeBound X (n^(k+1)) (A^(k+1)))
    (s : Finset (Fin N)) (hs : s.card ≤ n^(k+1))
    (x : Fin N → X) (hx0 : ∀ i, i ∉ s → x i = 0)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ (r⁻¹)^k) :
    cubeL2 X (rademacherSum X x) ≤
      Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := by
  classical
  set M := n ^ (k + 1) with hM
  let oe : Fin s.card ↪ Fin N := (s.orderEmbOfFin rfl).toEmbedding
  have hoe : ∀ j, oe j ∈ s := fun j => s.orderEmbOfFin_mem rfl j
  have hrange : ∀ i, i ∈ s → i ∈ Set.range oe := by
    intro i hi
    have : i ∈ Set.range (s.orderEmbOfFin rfl) := by
      rw [Finset.range_orderEmbOfFin]; exact hi
    exact this
  let z : Fin s.card → X := fun j => x (oe j)
  have e1 : cubeL2 X (rademacherSum X x) = cubeL2 X (rademacherSum X z) :=
    h50d_cubeL2_emb oe x z (fun j => rfl) (fun i hi => hx0 i (fun h => hi (hrange i h)))
  let ce : Fin s.card ↪ Fin M := Fin.castLEEmb hs
  let y : Fin M → X := Function.extend ce z 0
  have hy : ∀ j, y (ce j) = z j := fun j => ce.injective.extend_apply _ _ _
  have hy0 : ∀ k, k ∉ Set.range ce → y k = 0 := by
    intro k hk
    exact Function.extend_apply' _ _ _ (fun ⟨a, ha⟩ => hk ⟨a, ha⟩)
  have e2 : cubeL2 X (rademacherSum X y) = cubeL2 X (rademacherSum X z) :=
    h50d_cubeL2_emb ce y z hy hy0
  have hsum : ∑ i, ‖y i‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 :=
    h50d_sum_emb ce y z hy hy0 (fun _ v => ‖v‖ ^ 2) (fun _ => by simp)
  have hzb : ∀ j, ‖z j‖ ^ 2 ≤ ((r⁻¹) ^ k) ^ 2 := by
    intro j
    exact pow_le_pow_left₀ (norm_nonneg _) (hx _ (hoe j)) 2
  have hzs : ∑ j, ‖z j‖ ^ 2 ≤ (M : ℝ) * ((r⁻¹) ^ k) ^ 2 := by
    calc ∑ j, ‖z j‖ ^ 2 ≤ ∑ _j : Fin s.card, ((r⁻¹) ^ k) ^ 2 := Finset.sum_le_sum fun j _ => hzb j
      _ = (s.card : ℝ) * ((r⁻¹) ^ k) ^ 2 := by simp
      _ ≤ (M : ℝ) * ((r⁻¹) ^ k) ^ 2 := by
        gcongr
  have hb := h y
  rw [e2, hsum] at hb
  rw [e1]
  have hAn : 0 ≤ A * n := mul_nonneg hA (Nat.cast_nonneg n)
  have hR : 0 ≤ Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k := by positivity
  have hL : 0 ≤ cubeL2 X (rademacherSum X z) := Real.sqrt_nonneg _
  refine (pow_le_pow_iff_left₀ hL hR (by norm_num : (2:ℕ) ≠ 0)).mp ?_
  calc cubeL2 X (rademacherSum X z) ^ 2 ≤ A ^ (k+1) * ∑ j, ‖z j‖ ^ 2 := hb
    _ ≤ A ^ (k+1) * ((M : ℝ) * ((r⁻¹) ^ k) ^ 2) := by gcongr
    _ = (Real.sqrt (A*n)*(Real.sqrt (A*n)*r⁻¹)^k) ^ 2 := by
      have hq : Real.sqrt (A*n) ^ 2 = A*n := Real.sq_sqrt hAn
      calc A ^ (k+1) * ((M : ℝ) * ((r⁻¹) ^ k) ^ 2) = (A*n)^(k+1) * ((r⁻¹) ^ k) ^ 2 := by
            rw [hM]; push_cast; ring
        _ = (Real.sqrt (A*n) ^ 2)^(k+1) * ((r⁻¹) ^ k) ^ 2 := by rw [hq]
        _ = _ := by ring

