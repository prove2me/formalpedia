-- Prove2me | solution 1 for OAI.Dixmier.DirectSumObstruction.scaled_direct_sum_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:01:13.045744+00:00
-- url     : https://prove2.me/submissions/de7c834a-9ceb-4937-8fd4-107d1cf22a9b

-- Generated from openai/math@1581d4c lean/OAI/Analysis/Unitarizability/ScaledObstruction.lean:L28-L61
-- (upload_full_project.md Phase 4): solution for node OAI.Dixmier.DirectSumObstruction.scaled_direct_sum_obstruction. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelEnergy__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_KernelObstruction__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Cocycle__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_HilbertSum__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_Triangular__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_InvariantProjection__DixmierAllDiscrete
import Definitions.Def_OAI_Analysis_Unitarizability_SumObstruction__DixmierAllDiscrete

-- ---- from OAI.Analysis.Unitarizability.KernelObstruction ----
namespace OAI

/-! Coordinate maps and the invariant-kernel obstruction.
The Hilbert space is the lp space with finite Euclidean fibres. -/
noncomputable section
namespace Dixmier
namespace KernelObstruction
open scoped ComplexConjugate
open Finset
variable {G K : Type*} [Fintype K]
attribute [local instance] OAI.Dixmier.KernelObstruction.instDecidableEq_oAI_1
theorem inclusion_opNorm_le (x : G) : ‖inclusion (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  simp

theorem evaluation_opNorm_le (x : G) : ‖evaluation (K := K) x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro ξ
  simpa using lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) ξ x

theorem coefficients_norm_sq (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B‖^2 = ∑ b : K, ‖B (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, coefficients_apply]
  exact Finset.sum_comm

theorem space_summable (ξ : Space G K) : Summable (fun x => ‖ξ x‖^2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem column_summable (L : Fibre K →L[ℂ] Space G K) :
    Summable (fun x => ‖coefficients ((evaluation x).comp L)‖^2) := by
  simp_rw [coefficients_norm_sq]
  exact summable_sum (fun b _ => space_summable (L (EuclideanSpace.basisFun K ℂ b)))

theorem column_energy (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 =
      ∑ b : K, ‖L (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp_rw [coefficients_norm_sq]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro b hb
    exact (space_norm_sq _).symm
  · intro b hb
    exact space_summable _

theorem column_energy_le (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 ≤
      (Fintype.card K : ℝ) * ‖L‖^2 := by
  rw [column_energy]
  calc
    _ ≤ ∑ b : K, ‖L‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have h := L.le_opNorm (EuclideanSpace.basisFun K ℂ b)
      simp only [(EuclideanSpace.basisFun K ℂ).norm_eq_one, mul_one] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by simp [nsmul_eq_mul]

theorem coefficients_adjoint_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B.adjoint (a,b) = conj (coefficients B (b,a)) := by
  simp only [coefficients_apply]
  rw [← EuclideanSpace.basisFun_inner, ← EuclideanSpace.basisFun_inner]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem coefficients_adjoint_norm (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B.adjoint‖ = ‖coefficients B‖ := by
  have h : ‖coefficients B.adjoint‖^2 = ‖coefficients B‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      coefficients_adjoint_apply, RCLike.norm_conj]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (coefficients B.adjoint), norm_nonneg (coefficients B)]

theorem row_block_norm (R : Space G K →L[ℂ] Fibre K) (x : G) :
    ‖coefficients (R.comp (inclusion x))‖ =
      ‖coefficients ((evaluation x).comp R.adjoint)‖ := by
  rw [← coefficients_adjoint_norm (R.comp (inclusion x)),
    ContinuousLinearMap.adjoint_comp, inclusion_adjoint]

theorem row_summable (R : Space G K →L[ℂ] Fibre K) :
    Summable (fun x => ‖coefficients (R.comp (inclusion x))‖^2) := by
  simp_rw [row_block_norm]
  exact column_summable R.adjoint

theorem row_energy_le (R : Space G K →L[ℂ] Fibre K) :
    ∑' x, ‖coefficients (R.comp (inclusion x))‖^2 ≤
      (Fintype.card K : ℝ) * ‖R‖^2 := by
  simp_rw [row_block_norm]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using column_energy_le R.adjoint

variable [Group G]

theorem block_invariant {F : Op G K} (hF : F ∈ Commutant) (g x y : G) :
    block F (g*x) (g*y) = block F x y := by
  ext v a
  have h := congrArg (fun B : Op G K => B (inclusion y v) (g*x)) (hF g).eq
  simp only [mul_apply_eq_comp, translation_inclusion, translation_apply,
    inv_mul_cancel_left] at h
  exact congrArg (fun v : Fibre K => v a) h

theorem block_kernel {F : Op G K} (hF : F ∈ Commutant) (x y : G) :
    block F x y = block F 1 (x⁻¹*y) := by
  simpa only [mul_one, mul_inv_cancel_left] using block_invariant hF x 1 (x⁻¹*y)

theorem commutant_sub {A C : Op G K} (hA : A ∈ Commutant) (hC : C ∈ Commutant) :
    A-C ∈ Commutant := by
  intro g
  change (A-C) * translation g = translation g * (A-C)
  simp only [sub_mul, mul_sub, (hA g).eq, (hC g).eq]

theorem energy_summable (A : Op G K) :
    Summable (fun s => ‖coefficients (block A 1 s)‖^2) :=
  row_summable (row A 1)

theorem energy_le_row (A : Op G K) :
    energy A ≤ (Fintype.card K : ℝ) * ‖row A 1‖^2 :=
  row_energy_le (row A 1)

theorem energy_eq_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A = ∑' x, ‖coefficients ((evaluation x).comp (col A 1))‖^2 := by
  change (∑' s, ‖coefficients (block A 1 s)‖^2) = ∑' x, ‖coefficients (block A x 1)‖^2
  simp_rw [block_kernel hA _ 1, mul_one]
  exact ((Equiv.inv G).tsum_eq (fun s => ‖coefficients (block A 1 s)‖^2)).symm

theorem energy_le_column {A : Op G K} (hA : A ∈ Commutant) :
    energy A ≤ (Fintype.card K : ℝ) * ‖col A 1‖^2 := by
  rw [energy_eq_column hA]
  exact column_energy_le _

omit [Group G] in
theorem row_norm_le (F : Op G K) (x : G) : ‖row F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (evaluation_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem col_norm_le (F : Op G K) (x : G) : ‖col F x‖ ≤ ‖F‖ := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_left (inclusion_opNorm_le (K := K) x) (norm_nonneg F))

omit [Group G] in
theorem row_difference_bound (T C : Op G K) (x : G) :
    ‖row C x‖ ≤ ‖row T x‖ + ‖T-C‖ := by
  have h : row C x = row T x - row (T-C) x := by ext v a; simp [row]
  rw [h]
  exact (norm_sub_le _ _).trans (add_le_add (le_refl _) (row_norm_le _ _))

omit [Group G] in
theorem col_difference_bound (A T C : Op G K) (x : G) :
    ‖col (A-C) x‖ ≤ ‖col (A-T) x‖ + ‖T-C‖ := by
  have h : col (A-C) x = col (A-T) x + col (T-C) x := by
    ext v y a
    simp [col]
  rw [h]
  exact (norm_add_le _ _).trans (add_le_add (le_refl _) (col_norm_le _ _))

theorem energy_split_le (A C : Op G K) : energy A ≤ 2 * energy C + 2 * energy (A-C) := by
  have hp (s : G) : ‖coefficients (block A 1 s)‖^2 ≤
      2 * ‖coefficients (block C 1 s)‖^2 + 2 * ‖coefficients (block (A-C) 1 s)‖^2 := by
    rw [block_sub, coefficients_sub]
    have ht := norm_add_le (coefficients (block C 1 s))
      (coefficients (block A 1 s) - coefficients (block C 1 s))
    rw [add_sub_cancel] at ht
    nlinarith [norm_nonneg (coefficients (block A 1 s)),
      norm_nonneg (coefficients (block C 1 s)),
      norm_nonneg (coefficients (block A 1 s) - coefficients (block C 1 s)),
      sq_nonneg (‖coefficients (block C 1 s)‖ -
        ‖coefficients (block A 1 s) - coefficients (block C 1 s)‖)]
  have hs := ((energy_summable C).mul_left 2).add ((energy_summable (A-C)).mul_left 2)
  have h := (energy_summable A).tsum_le_tsum hp hs
  rw [((energy_summable C).mul_left 2).tsum_add ((energy_summable (A-C)).mul_left 2),
    tsum_mul_left, tsum_mul_left] at h
  exact h

/-- The kernel-energy obstruction, proved from coordinate estimates and commutation. -/
theorem kernel_obstruction {A T : Op G K} (hA : A ∈ Commutant)
    {κ : ℝ} (_hκ : 0 ≤ κ) (hr : ‖row T 1‖ ≤ κ) (hc : ‖col (A-T) 1‖ ≤ κ)
    {C : Op G K} (hC : C ∈ Commutant) :
    energy A ≤ 4 * (Fintype.card K : ℝ) * (κ + ‖T-C‖)^2 := by
  have hR : ‖row C 1‖ ≤ κ + ‖T-C‖ :=
    (row_difference_bound T C 1).trans (add_le_add hr (le_refl _))
  have hL : ‖col (A-C) 1‖ ≤ κ + ‖T-C‖ :=
    (col_difference_bound A T C 1).trans (add_le_add hc (le_refl _))
  have heC := (energy_le_row C).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hR 2) (Nat.cast_nonneg (Fintype.card K)))
  have heAC := (energy_le_column (commutant_sub hA hC)).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) hL 2) (Nat.cast_nonneg (Fintype.card K)))
  nlinarith [energy_split_le A C]

end KernelObstruction
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Cocycle ----
namespace OAI

/-! Cocycle algebra in an arbitrary ring, specializing to bounded complex Hilbert-space operators. -/
namespace Dixmier
section Ring
variable {G R : Type*} [Group G] [Ring R]

theorem conjugate_mul (U : G →* R) (g h : G) (T : R) :
    conjugate U (g * h) T = conjugate U g (conjugate U h T) := by
  simp [conjugate, map_mul, mul_assoc]

theorem conjugate_sub (U : G →* R) (g : G) (A B : R) :
    conjugate U g (A - B) = conjugate U g A - conjugate U g B := by
  simp [conjugate, mul_sub, sub_mul]

/-- The coboundary cocycle identity, before taking direct sums. -/
theorem coboundary_cocycle (U : G →* R) (T : R) (g h : G) :
    coboundary U T (g * h) = coboundary U T g + conjugate U g (coboundary U T h) := by
  simp only [coboundary, conjugate_mul, conjugate_sub]
  abel

theorem conjugate_eq_self_iff_commute (U : G →* R) (g : G) (T : R) :
    conjugate U g T = T ↔ Commute (U g) T := by
  have hinv : U g⁻¹ * U g = 1 := by rw [← map_mul]; simp
  have hginv : U g * U g⁻¹ = 1 := by rw [← map_mul]; simp
  constructor
  · intro h
    have hh := congrArg (fun x : R => x * U g) h
    change U g * T = T * U g
    simpa [conjugate, mul_assoc, hinv] using hh
  · intro h
    change U g * T * U g⁻¹ = T
    rw [h.eq, mul_assoc, hginv, mul_one]

/-- Comparing the two implementers gives the commutant element T - B. -/
theorem equal_coboundaries_iff_commute_sub (U : G →* R) (T B : R) (g : G) :
    coboundary U T g = coboundary U B g ↔ Commute (U g) (T - B) := by
  rw [← conjugate_eq_self_iff_commute, conjugate_sub]
  simp only [coboundary]
  constructor
  · intro h
    calc
      conjugate U g T - conjugate U g B =
          (T - (T - conjugate U g T)) - (B - (B - conjugate U g B)) := by abel
      _ = T - B := by rw [h]; abel
  · intro h
    calc
      T - conjugate U g T = B - conjugate U g B +
          ((T - B) - (conjugate U g T - conjugate U g B)) := by abel
      _ = B - conjugate U g B := by rw [h]; abel

end Ring
end Dixmier

end OAI

-- ---- from OAI.Analysis.Unitarizability.HilbertSum ----
namespace OAI

/-! Uniformly bounded Hilbert direct sums. The component implementers
are never summed and need not be uniformly bounded. -/
noncomputable section
namespace Dixmier
namespace HilbertSum
variable {G I : Type*} [Group G] {E : I → Type*}
variable [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
attribute [local instance] OAI.Dixmier.HilbertSum.instDecidableEq_oAI
theorem boundedSum_norm_le (T : ∀ i, E i →L[ℂ] E i) {κ : ℝ}
    (hκ : 0 ≤ κ) (hT : ∀ i, ‖T i‖ ≤ κ) : ‖boundedSum T hκ hT‖ ≤ κ :=
  lp.norm_mapCLM_le 2 T hκ hT

theorem representation_norm_map (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (x : Space E) :
    ‖representation U hU g x‖ = ‖x‖ := by
  have hs : ‖representation U hU g x‖^2 = ‖x‖^2 := by
    have norm_sq (y : Space E) : ‖y‖^2 = ∑' i, ‖y i‖^2 := by
      simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) y
    simp only [norm_sq, representation_apply, hU]
  nlinarith [norm_nonneg (representation U hU g x), norm_nonneg x]

theorem cocycle_one (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (h1 : ∀ i, D i 1 = 0) :
    cocycle D hκ hb 1 = 0 := by ext x i; simp [h1]

theorem cocycle_identity (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ)
    (hD : ∀ i g h, D i (g*h) = D i g + conjugate (U i) g (D i h)) (g h : G) :
    cocycle D hκ hb (g*h) = cocycle D hκ hb g +
      conjugate (representation U hU) g (cocycle D hκ hb h) := by
  ext x i
  change D i (g*h) (x i) = D i g (x i) + U i g (D i h (U i g⁻¹ (x i)))
  rw [hD]
  rfl

theorem representation_inclusion (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (g : G) (i : I) (x : E i) :
    representation U hU g (inclusion i x) = inclusion i (U i g x) := by
  ext j
  by_cases h : j = i
  · subst j; simp
  · simp [Pi.single_eq_of_ne h]

theorem compression_norm_le (B : Space E →L[ℂ] Space E) (i : I) : ‖compression B i‖ ≤ ‖B‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg B)
  intro x
  change ‖B (lp.single 2 i x) i‖ ≤ ‖B‖ * ‖x‖
  calc
    _ ≤ ‖B (lp.single 2 i x)‖ := lp.norm_apply_le_norm (by norm_num) _ i
    _ ≤ ‖B‖ * ‖lp.single 2 i x‖ := B.le_opNorm _
    _ = _ := by rw [lp.norm_single (by norm_num : (0 : ENNReal) < 2)]

theorem compression_conjugate (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (B : Space E →L[ℂ] Space E) (i : I) (g : G) :
    compression (conjugate (representation U hU) g B) i =
      conjugate (U i) g (compression B i) := by
  ext x
  change (representation U hU g (B (representation U hU g⁻¹ (inclusion i x)))) i = _
  rw [representation_inclusion, representation_apply]
  rfl

theorem compression_implementer (U : ∀ i, G →* (E i →L[ℂ] E i))
    (hU : ∀ i g x, ‖U i g x‖ = ‖x‖) (D : ∀ i, G → (E i →L[ℂ] E i)) {κ : ℝ}
    (hκ : 0 ≤ κ) (hb : ∀ i g, ‖D i g‖ ≤ κ) (B : Space E →L[ℂ] Space E)
    (hB : ∀ g, cocycle D hκ hb g = coboundary (representation U hU) B g) (i : I) (g : G) :
    D i g = coboundary (U i) (compression B i) g := by
  have h := congrArg (fun T => compression T i) (hB g)
  have hc : compression (cocycle D hκ hb g) i = D i g := by
    ext x
    change D i g (lp.single 2 i x i) = D i g x
    rw [lp.single_apply_self]
  have hs (A C : Space E →L[ℂ] Space E) : compression (A-C) i = compression A i - compression C i := by
    ext x; rfl
  rwa [hc, coboundary, hs, compression_conjugate] at h

end HilbertSum
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Triangular ----
namespace OAI

/-! Bounded Hilbert sums and triangular representations. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H]
theorem diagonal_norm_map (U : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) (x : Double H) :
    ‖diagonal U x‖ = ‖x‖ := by
  have h : ‖diagonal U x‖^2 = ‖x‖^2 := by
    simp only [WithLp.prod_norm_sq_eq_of_L2, diagonal_fst, diagonal_snd, hU]
  nlinarith [norm_nonneg (diagonal U x), norm_nonneg x]

theorem operator_norm_le (U D : H →L[ℂ] H) (hU : ∀ x, ‖U x‖ = ‖x‖) :
    ‖operator U D‖ ≤ 1 + ‖D‖ := by
  have hd : ‖diagonal U‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp [diagonal_norm_map U hU]
  have hn : ‖inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H)))‖ ≤ ‖D‖ := by
    apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg D)
    intro x
    change ‖inl (D (U x.snd))‖ ≤ ‖D‖ * ‖x‖
    rw [inl_norm]
    calc
      ‖D (U x.snd)‖ ≤ ‖D‖ * ‖U x.snd‖ := D.le_opNorm _
      _ = ‖D‖ * ‖x.snd‖ := by rw [hU]
      _ ≤ ‖D‖ * ‖x‖ := mul_le_mul_of_nonneg_left (WithLp.norm_snd_le H x) (norm_nonneg D)
  exact (norm_add_le (diagonal U) (inl.comp (D.comp (U.comp (WithLp.sndL 2 ℂ H H))))).trans
    (add_le_add hd hn)

theorem representation_bound (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) {κ : ℝ} (hb : ∀ g, ‖D g‖ ≤ κ) (g : G) :
    ‖representation U D h1 hD g‖ ≤ 1 + κ :=
  (operator_norm_le (U g) (D g) (hU g)).trans (add_le_add (le_refl _) (hb g))

end Triangular
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.InvariantProjection ----
namespace OAI

/-! A unitarizing similarity gives a bounded commuting projection
onto every closed invariant subspace. -/
noncomputable section
namespace Dixmier
namespace InvariantProjection
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem orthogonal_projection_commutes (U : G →* (H →L[ℂ] H))
    (hU : ∀ g x, ‖U g x‖ = ‖x‖) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → U g x ∈ M) (g : G) :
    Commute M.toSubmodule.starProjection (U g) := by
  change M.toSubmodule.starProjection * U g = U g * M.toSubmodule.starProjection
  apply ContinuousLinearMap.ext
  intro x
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact hM g _ (Submodule.starProjection_apply_mem _ _)
  · intro w hw
    have hi := (LinearMap.norm_map_iff_inner_map_map (U g)).mp (hU g)
    have hm : U g⁻¹ w ∈ M := hM g⁻¹ w hw
    have hz := M.toSubmodule.starProjection_inner_eq_zero x (U g⁻¹ w) hm
    have he := hi (x - M.toSubmodule.starProjection x) (U g⁻¹ w)
    rw [map_sub, rep_inv] at he
    exact he.trans hz

/-- The conclusion supplies one bounded projection; it assumes only the
actual similarity and closed invariance, not a cocycle implementer. -/
theorem exists_commuting_projection (π : G →* (H →L[ℂ] H))
    (hπ : SimilarToUnitary π) (M : ClosedSubmodule ℂ H)
    (hM : ∀ g x, x ∈ M → π g x ∈ M) :
    ∃ P : H →L[ℂ] H, (∀ x, P x ∈ M) ∧
      (∀ x, x ∈ M → P x = x) ∧ ∀ g, Commute P (π g) := by
  rcases hπ with ⟨S, hS⟩
  let N : ClosedSubmodule ℂ H := M.mapEquiv S
  have hN : ∀ g x, x ∈ N → conjugated π S g x ∈ N := by
    intro g x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact ⟨π g y, hM g y hy, by simp⟩
  let Q := N.toSubmodule.starProjection
  let P : H →L[ℂ] H := S.symm.toContinuousLinearMap.comp (Q.comp S.toContinuousLinearMap)
  have hmem (x : H) : P x ∈ M := by
    have h := Submodule.starProjection_apply_mem N.toSubmodule (S x)
    rcases h with ⟨y, hy, he⟩
    change S.symm (Q (S x)) ∈ M
    rw [← he]
    simpa using hy
  have hfix (x : H) (hx : x ∈ M) : P x = x := by
    have hn : S x ∈ N := ⟨x, hx, rfl⟩
    change S.symm (Q (S x)) = x
    rw [Submodule.starProjection_eq_self_iff.mpr hn]
    simp
  refine ⟨P, hmem, hfix, ?_⟩
  intro g
  have hq := orthogonal_projection_commutes (conjugated π S) hS N hN g
  change P * π g = π g * P
  ext x
  have h := congrArg (fun T : H →L[ℂ] H => S.symm (T (S x))) hq.eq
  simpa [P, Q, mul_apply_eq_comp] using h

end InvariantProjection
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.Unitarizer ----
namespace OAI

/-! The bounded implementer forced by a unitarizing similarity.
The commuting projection onto H ⊕ 0 has upper-right block equal to the
negative implementer, avoiding a bounded inverse for graph coordinates. -/
noncomputable section
namespace Dixmier
namespace Triangular
variable {G H : Type*} [Group G]
variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A global cocycle implementer obtained from the similarity itself. -/
theorem implementer_of_similar (U : G →* (H →L[ℂ] H)) (D : G → (H →L[ℂ] H))
    (h1 : D 1 = 0) (hD : ∀ g h, D (g*h) = D g + conjugate U g (D h))
    (hπ : SimilarToUnitary (representation U D h1 hD)) :
    ∃ B : H →L[ℂ] H, ∀ g, D g = coboundary U B g := by
  let π := representation U D h1 hD
  let M : ClosedSubmodule ℂ (Double H) :=
    ⟨(WithLp.sndL 2 ℂ H H).ker, (WithLp.sndL 2 ℂ H H).isClosed_ker⟩
  have hM : ∀ g x, x ∈ M → π g x ∈ M := by
    intro g x hx
    change x.snd = 0 at hx
    change (operator (U g) (D g) x).snd = 0
    simp [hx]
  rcases InvariantProjection.exists_commuting_projection π hπ M hM with ⟨P, hm, hf, hp⟩
  let q : H →L[ℂ] H := (WithLp.fstL 2 ℂ H H).comp (P.comp inr)
  have hzero (x : Double H) : (P x).snd = 0 := hm x
  have hfix (x : H) : P (inl x) = inl x := hf _ (by change (inl x).snd = 0; simp)
  have hdecomp (x : Double H) : x = inl x.fst + inr x.snd := by
    apply (WithLp.equiv 2 (H × H)).injective
    apply Prod.ext <;> simp
  have hfst (x : Double H) : (P x).fst = x.fst + q x.snd := by
    nth_rw 1 [hdecomp x]
    rw [map_add, hfix]
    simp [q]
  refine ⟨-q, ?_⟩
  intro g
  ext x
  have h := congrArg (fun T : Double H →L[ℂ] Double H => (T (inr (U g⁻¹ x))).fst) (hp g).eq
  change (P (operator (U g) (D g) (inr (U g⁻¹ x)))).fst =
    (operator (U g) (D g) (P (inr (U g⁻¹ x)))).fst at h
  rw [hfst, operator_fst, operator_snd, operator_fst, hzero] at h
  have hinv : U g (U g⁻¹ x) = x := InvariantProjection.rep_inv U g x
  simp only [inr_apply, WithLp.toLp_fst, WithLp.toLp_snd, map_zero, zero_add, hinv,
    add_zero] at h
  change D g x = (-q) x - U g ((-q) (U g⁻¹ x))
  simp only [neg_apply, map_neg, sub_neg_eq_add]
  change D g x + q x = U g (q (U g⁻¹ x)) at h
  apply eq_neg_add_iff_add_eq.mpr
  simpa only [add_comm] using h

end Triangular
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.SumObstruction ----
namespace OAI

/-! The operator-theoretic direct-sum obstruction, constructed from stage operators
without any uniform bound on their norms. -/
noncomputable section
namespace Dixmier
namespace DirectSumObstruction
open Filter
open scoped Topology
variable {G : Type*} [Group G]

theorem stage_unitary (k : ℕ → ℕ) (j : ℕ) (g : G) (x : Stage G k j) :
    ‖KernelObstruction.translation g x‖ = ‖x‖ :=
  KernelObstruction.reindex_norm (Equiv.mulLeft g⁻¹) x

/-- The direct-sum obstruction with its representation and bound.
The stage operators A_j and T_j need not be uniformly bounded. -/
theorem direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j-T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + κ) ∧ ¬ SimilarToUnitary π := by
  let U : ∀ j, G →* (Stage G k j →L[ℂ] Stage G k j) := fun _ => KernelObstruction.translation
  have hU : ∀ j g x, ‖U j g x‖ = ‖x‖ := stage_unitary k
  let D : ∀ j, G → (Stage G k j →L[ℂ] Stage G k j) := fun j => coboundary (U j) (T j)
  have h1 : ∀ j, D j 1 = 0 := fun j => coboundary_one (U j) (T j)
  have hD : ∀ j g h, D j (g*h) = D j g + conjugate (U j) g (D j h) :=
    fun j => coboundary_cocycle (U j) (T j)
  let V := HilbertSum.representation U hU
  let δ := HilbertSum.cocycle D hκ hb
  have hδ1 : δ 1 = 0 := HilbertSum.cocycle_one D hκ hb h1
  have hδ : ∀ g h, δ (g*h) = δ g + conjugate V g (δ h) :=
    HilbertSum.cocycle_identity U hU D hκ hb hD
  let π := Triangular.representation V δ hδ1 hδ
  have hδb : ∀ g, ‖δ g‖ ≤ κ := fun g => HilbertSum.boundedSum_norm_le _ hκ _
  refine ⟨π, Triangular.representation_bound V δ hδ1 hδ
    (HilbertSum.representation_norm_map U hU) hδb, ?_⟩
  intro hπ
  rcases Triangular.implementer_of_similar V δ hδ1 hδ hπ with ⟨B, hB⟩
  have hbound (j : ℕ) : KernelObstruction.energy (A j) / k j ≤ 4 * (κ + ‖B‖)^2 := by
    let Bj := HilbertSum.compression B j
    have hBj (g : G) : D j g = coboundary (U j) Bj g :=
      HilbertSum.compression_implementer U hU D hκ hb B hB j g
    have hC : T j - Bj ∈ KernelObstruction.Commutant := by
      intro g
      exact ((equal_coboundaries_iff_commute_sub (U j) (T j) Bj g).mp (hBj g)).symm
    have henergy := KernelObstruction.kernel_obstruction (hA j) hκ (hr j) (hc j) hC
    simp only [Fintype.card_fin, sub_sub_cancel] at henergy
    have hnorm : ‖Bj‖ ≤ ‖B‖ := HilbertSum.compression_norm_le B j
    have hs : (κ + ‖Bj‖)^2 ≤ (κ + ‖B‖)^2 :=
      pow_le_pow_left₀ (add_nonneg hκ (norm_nonneg _)) (add_le_add (le_refl _) hnorm) 2
    have henergy' : KernelObstruction.energy (A j) ≤ 4 * (k j : ℝ) * (κ + ‖B‖)^2 :=
      henergy.trans (mul_le_mul_of_nonneg_left hs (by positivity))
    apply (div_le_iff₀ (Nat.cast_pos.mpr (hk j))).mpr
    nlinarith [henergy']
  obtain ⟨j, hj⟩ := (he.eventually (eventually_gt_atTop (4 * (κ + ‖B‖)^2))).exists
  exact (not_lt_of_ge (hbound j)) hj

end DirectSumObstruction
end Dixmier

end

end OAI

-- ---- from OAI.Analysis.Unitarizability.ScaledObstruction ----
namespace OAI

noncomputable section
namespace Dixmier
namespace KernelObstruction
variable {G K : Type*} [Group G] [Fintype K]

lemma coefficients_real_smul (t : ℝ) (B : Fibre K →L[ℂ] Fibre K) :
    coefficients (t • B) = t • coefficients B := by
  ext ab
  rfl

lemma energy_real_smul (t : ℝ) (A : Op G K) : energy (t • A) = t ^ 2 * energy A := by
  have hb (x y : G) : block (t • A) x y = t • block A x y := by
    simp only [block, ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
  simp only [energy, hb, coefficients_real_smul, norm_smul, Real.norm_eq_abs,
    mul_pow, sq_abs]
  exact tsum_mul_left

end KernelObstruction
namespace DirectSumObstruction
open Filter
variable {G : Type*} [Group G]

theorem scaled_direct_sum_obstruction (k : ℕ → ℕ) (hk : ∀ j, 0 < k j)
    (A T : ∀ j, Stage G k j →L[ℂ] Stage G k j)
    (hA : ∀ j, A j ∈ KernelObstruction.Commutant)
    {κ : ℝ} (hκ : 0 ≤ κ)
    (hr : ∀ j, ‖KernelObstruction.row (T j) 1‖ ≤ κ)
    (hc : ∀ j, ‖KernelObstruction.col (A j - T j) 1‖ ≤ κ)
    (hb : ∀ j g, ‖coboundary KernelObstruction.translation (T j) g‖ ≤ κ)
    (he : Tendsto (fun j => KernelObstruction.energy (A j) / k j) atTop atTop)
    {t : ℝ} (ht : 0 < t) :
    ∃ π : G →* (Carrier G k →L[ℂ] Carrier G k),
      (∀ g, ‖π g‖ ≤ 1 + t * κ) ∧ ¬ SimilarToUnitary π := by
  apply direct_sum_obstruction k hk (fun j => t • A j) (fun j => t • T j)
    (fun j g => by
      change (t • A j).comp (KernelObstruction.translation g) =
        (KernelObstruction.translation g).comp (t • A j)
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
      exact congrArg (fun operator => t • operator) (hA j g).eq)
    (mul_nonneg ht.le hκ)
  · intro j
    simpa only [KernelObstruction.row, ContinuousLinearMap.comp_smul,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht] using mul_le_mul_of_nonneg_left (hr j) ht.le
  · intro j
    rw [← smul_sub t (A j) (T j)]
    simpa only [KernelObstruction.col, ContinuousLinearMap.smul_comp,
      norm_smul, Real.norm_eq_abs, abs_of_pos ht] using mul_le_mul_of_nonneg_left (hc j) ht.le
  · intro j g
    have hscale : coboundary KernelObstruction.translation (t • T j) g =
        t • coboundary KernelObstruction.translation (T j) g := by
      simp only [coboundary, conjugate, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp, smul_sub]
    rw [hscale, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    exact mul_le_mul_of_nonneg_left (hb j g) ht.le
  · simpa only [KernelObstruction.energy_real_smul, mul_div_assoc] using
      he.const_mul_atTop (sq_pos_of_pos ht)

end DirectSumObstruction

end Dixmier
end

end OAI

-- ---- platform node ----
open OAI OAI.Dixmier OAI.Dixmier.DirectSumObstruction
open Filter


theorem solution : type_of% @_root_.OAI.Dixmier.DirectSumObstruction.scaled_direct_sum_obstruction := @_root_.OAI.Dixmier.DirectSumObstruction.scaled_direct_sum_obstruction
