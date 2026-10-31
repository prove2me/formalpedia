-- Prove2me | solution 1 for OAI.NuclearUltrapower.matched_vectors
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-30T14:36:12.927587+00:00
-- url     : https://prove2.me/submissions/fa48f464-77b7-4825-8196-c0c3daf0de35

import Mathlib
import Definitions.Def_OAIQ019N043

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_NuclearFiniteness
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzWords.instDecidableEqWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
universe u v w
open Filter
open scoped Topology InnerProductSpace ENNReal

noncomputable section

open scoped InnerProductSpace Topology
open Filter

namespace NuclearUltrapower
variable {Γ : Type u} {E : Type v}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem tupleEnergy_nonneg (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) :
    0 ≤ tupleEnergy S U x := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem tupleEnergy_bound (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) :
    tupleEnergy S U x ≤ 4 * (S.card : ℝ) * ‖x‖ ^ 2 := by
  calc
    _ ≤ ∑ s ∈ S, 4 * ‖x‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro s _
      have h := norm_sub_le (U s x) x
      rw [(U s).norm_map] at h
      nlinarith [norm_nonneg (U s x - x), norm_nonneg x]
    _ = _ := by simp; ring

theorem tupleEnergy_smul (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (c : ℂ) (x : E) :
    tupleEnergy S U (c • x) = ‖c‖ ^ 2 * tupleEnergy S U x := by
  simp only [tupleEnergy, map_smul, ← smul_sub, norm_smul, mul_pow, Finset.mul_sum]

theorem tupleEnergy_continuous (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    Continuous (tupleEnergy S U) := by
  unfold tupleEnergy
  fun_prop

variable [Nontrivial E]

theorem energyValues_nonempty (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    {r | ∃ x : E, ‖x‖ = 1 ∧ r = tupleEnergy S U x}.Nonempty := by
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  exact ⟨_, x, hx, rfl⟩

omit [Nontrivial E] in
theorem energyValues_bddBelow (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    BddBelow {r | ∃ x : E, ‖x‖ = 1 ∧ r = tupleEnergy S U x} := by
  refine ⟨0, ?_⟩
  rintro _ ⟨x, _, rfl⟩
  exact tupleEnergy_nonneg S U x

theorem bottomEnergy_nonneg (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    0 ≤ bottomEnergy S U :=
  le_csInf (energyValues_nonempty S U) (by rintro _ ⟨x, _, rfl⟩; exact tupleEnergy_nonneg S U x)

omit [Nontrivial E] in
theorem bottomEnergy_le (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) (hx : ‖x‖ = 1) :
    bottomEnergy S U ≤ tupleEnergy S U x :=
  csInf_le (energyValues_bddBelow S U) ⟨x, hx, rfl⟩

theorem bottomEnergy_bound (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) :
    bottomEnergy S U ≤ 4 * (S.card : ℝ) := by
  obtain ⟨x, hx⟩ := exists_norm_eq E zero_le_one
  have h := (bottomEnergy_le S U x hx).trans (tupleEnergy_bound S U x)
  simpa [hx] using h

omit [Nontrivial E] in
theorem bottomEnergy_mul_norm (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) (x : E) :
    bottomEnergy S U * ‖x‖ ^ 2 ≤ tupleEnergy S U x := by
  by_cases hx : x = 0
  · simp [hx, tupleEnergy]
  have hn : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hy : ‖(‖x‖⁻¹ : ℂ) • x‖ = 1 := by simp [norm_smul, norm_inv, hn]
  have h := bottomEnergy_le S U ((‖x‖⁻¹ : ℂ) • x) hy
  rw [tupleEnergy_smul] at h
  calc
    bottomEnergy S U * ‖x‖ ^ 2 ≤
        ‖(‖x‖⁻¹ : ℂ)‖ ^ 2 * tupleEnergy S U x * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right h (sq_nonneg ‖x‖)
    _ = tupleEnergy S U x := by
      rw [_root_.mul_right_comm]
      simp [norm_inv, hn]

theorem exists_energy_lt (S : Finset Γ) (U : Γ → E ≃ₗᵢ[ℂ] E) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : E, ‖x‖ = 1 ∧ tupleEnergy S U x < bottomEnergy S U + ε := by
  obtain ⟨r, ⟨x, hx, rfl⟩, hr⟩ := exists_lt_of_csInf_lt
    (energyValues_nonempty S U) (lt_add_of_pos_right (bottomEnergy S U) hε)
  exact ⟨x, hx, hr⟩

end NuclearUltrapower

namespace NuclearUltrapower

namespace HilbertUltraproduct
variable {ι : Type u} {E : ι → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (ω : Ultrafilter ι) {Γ : Type w}

/-- Finite Laplacian energies pass to the Hilbert ultraproduct exactly. -/
theorem tupleEnergy_tendsto (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (x : UltraPreHilbert E ω) :
    Tendsto (fun i => tupleEnergy S (fun g => U g i) (UltraPreHilbert.family ω x i))
      (ω : Filter ι) (𝓝 (tupleEnergy S (fun g => unitary ω (U g))
        (x : HilbertUltraproduct E ω))) := by
  unfold tupleEnergy
  apply tendsto_finsetSum
  intro s _
  have h := (UltraPreHilbert.norm_tendsto ω (preUnitary ω (U s) x - x)).pow 2
  convert h using 1
  · rfl
  · rw [unitary_coe, ← UniformSpace.Completion.coe_sub, UniformSpace.Completion.norm_coe]

variable [∀ i, Nontrivial (E i)]

/-- Bottom matching energies always have an ultralimit, with the
uniform upper bound 4 |S| and no dimension restriction. -/
theorem bottomEnergy_tendsto (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) :
    Tendsto (fun i => bottomEnergy S (fun g => U g i)) (ω : Filter ι)
      (𝓝 (limUnder (ω : Filter ι) (fun i => bottomEnergy S (fun g => U g i)))) := by
  apply hilbert_tendsto_ultralimit_of_bounded
  refine ⟨4 * (S.card : ℝ), fun i => ?_⟩
  rw [Real.norm_eq_abs, abs_of_nonneg (bottomEnergy_nonneg _ _)]
  exact bottomEnergy_bound _ _

omit [∀ i, Nontrivial (E i)] in
/-- Lower coordinate Rayleigh bounds pass to every vector of the completion,
not merely to vectors given by elementary tensors or bounded families. -/
theorem limit_energy_lower (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    {r : ℝ} (hr : Tendsto (fun i => bottomEnergy S (fun g => U g i))
      (ω : Filter ι) (𝓝 r)) (x : HilbertUltraproduct E ω) :
    r * ‖x‖ ^ 2 ≤ tupleEnergy S (fun g => unitary ω (U g)) x := by
  induction x using UniformSpace.Completion.induction_on with
  | hp => exact isClosed_le (by fun_prop) (tupleEnergy_continuous _ _)
  | ih x =>
    rw [UniformSpace.Completion.norm_coe]
    apply le_of_tendsto_of_tendsto (hr.mul ((UltraPreHilbert.norm_tendsto ω x).pow 2))
      (tupleEnergy_tendsto ω S U x)
    exact Filter.Eventually.of_forall (fun i => bottomEnergy_mul_norm _ _ _)

/-- Varying-dimensional spectral gap, expressed in the equivalent Rayleigh
formulation from the tensor-norm formulation. No uniform dimension bound and
no coordinate group relations are assumed. -/
theorem varying_gap [Group Γ] (S : Finset Γ) (κ : ℝ)
    (hgap : HasKazhdanGap.{w, max u v} S κ)
    (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g * h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ι) (𝓝 0))
    {r : ℝ} (hr : Tendsto (fun i => bottomEnergy S (fun g => U g i))
      (ω : Filter ι) (𝓝 r)) : r = 0 ∨ κ ≤ r ∧ r ≤ 4 * (S.card : ℝ) := by
  have hr0 : 0 ≤ r := ge_of_tendsto hr (Filter.Eventually.of_forall
    (fun i => bottomEnergy_nonneg S (fun g => U g i)))
  have hrR : r ≤ 4 * (S.card : ℝ) := le_of_tendsto hr (Filter.Eventually.of_forall
    (fun i => bottomEnergy_bound S (fun g => U g i)))
  by_cases hz : r = 0
  · exact Or.inl hz
  right
  refine ⟨?_, hrR⟩
  have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hz)
  let ρ := approximateRepresentation ω U h1 hmul
  have hno (x : HilbertUltraproduct E ω) (hx : ∀ g, ρ g x = x) : x = 0 := by
    have h := limit_energy_lower ω S U hr x
    have he : tupleEnergy S (fun g => unitary ω (U g)) x = 0 := by
      apply Finset.sum_eq_zero
      intro s _
      change ‖ρ s x - x‖ ^ 2 = 0
      rw [hx, sub_self, norm_zero, zero_pow (by decide)]
    rw [he] at h
    have hn : ‖x‖ = 0 := by
      have hs : ‖x‖ ^ 2 ≤ 0 := (mul_le_mul_iff_right₀ hrpos).mp (by simpa [mul_comm] using h)
      nlinarith [norm_nonneg x]
    exact norm_eq_zero.mp hn
  by_contra! hlt
  let ε := (κ - r) / 2
  have hε : 0 < ε := by dsimp [ε]; linarith
  choose x hx hxE using (fun i => exists_energy_lt S (fun g => U g i) hε)
  let y : UltraPreHilbert E ω := (⟨x, memℓp_infty ⟨1, by
    rintro _ ⟨i, rfl⟩; exact (hx i).le⟩⟩ : lp E ∞)
  have hyn : ‖y‖ = 1 := by
    apply tendsto_nhds_unique (UltraPreHilbert.norm_tendsto ω y)
    exact tendsto_const_nhds.congr (fun i => (hx i).symm)
  have hbound : tupleEnergy S (fun g => unitary ω (U g)) (y : HilbertUltraproduct E ω)
      ≤ r + ε := by
    apply le_of_tendsto_of_tendsto (tupleEnergy_tendsto ω S U y) (hr.add_const ε)
    exact Filter.Eventually.of_forall (fun i => (hxE i).le)
  have hg := hgap (HilbertUltraproduct E ω) ρ hno (y : HilbertUltraproduct E ω)
  rw [UniformSpace.Completion.norm_coe, hyn, one_pow, mul_one] at hg
  change κ ≤ tupleEnergy S (fun g => unitary ω (U g)) (y : HilbertUltraproduct E ω) at hg
  dsimp [ε] at hbound
  linarith

end HilbertUltraproduct
end NuclearUltrapower
end
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_InducedApproximation
attribute [-instance] _root_.OAI.NuclearUltrapower.CuntzPolynomial.instInvolutiveStarWord _root_.OAI.NuclearUltrapower.CuntzPolynomial.instStarWord _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v w
section ApproxInvariant
variable {ι : Type u} {Γ : Type v} [Group Γ] {E : ι → Type w}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (l : Filter ι) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : ∀ i, E i)

theorem displacement_product_le (g h : Γ) (i : ι) :
    ‖U (g*h) i (x i)-x i‖ ≤
      ‖(U (g*h) i : E i →L[ℂ] E i) - ((U g i * U h i) : E i →L[ℂ] E i)‖ * ‖x i‖ +
      ‖U g i (x i)-x i‖ + ‖U h i (x i)-x i‖ := by
  calc
    ‖U (g*h) i (x i)-x i‖ ≤
        ‖U (g*h) i (x i) - U g i (U h i (x i))‖ +
        ‖U g i (U h i (x i)) - U g i (x i)‖ + ‖U g i (x i)-x i‖ := by
      have ht := norm_add_le (U (g*h) i (x i)-U g i (U h i (x i)))
        (U g i (U h i (x i))-U g i (x i))
      have hs := norm_add_le ((U (g*h) i (x i)-U g i (U h i (x i))) +
        (U g i (U h i (x i))-U g i (x i))) (U g i (x i)-x i)
      simp only [sub_add_sub_cancel] at ht hs
      linarith
    _ ≤ _ := by
      rw [← map_sub, (U g i).norm_map]
      have ht := ContinuousLinearMap.le_opNorm
        ((U (g*h) i : E i →L[ℂ] E i)-((U g i * U h i) : E i →L[ℂ] E i)) (x i)
      change ‖U (g*h) i (x i)-U g i (U h i (x i))‖ ≤ _ at ht
      linarith

variable {l U x}

theorem almostInvariant_mul {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    {g h : Γ} (hg : AlmostInvariant l U x g) (hh : AlmostInvariant l U x h) :
    AlmostInvariant l U x (g*h) := by
  have hb (i : ι) : ‖U (g*h) i (x i)-x i‖ ≤
      ‖(U (g*h) i : E i →L[ℂ] E i)-((U g i * U h i) : E i →L[ℂ] E i)‖ * C +
      ‖U g i (x i)-x i‖ + ‖U h i (x i)-x i‖ := by
    have hle := mul_le_mul_of_nonneg_left (hx i)
      (norm_nonneg ((U (g*h) i : E i →L[ℂ] E i)-((U g i * U h i) : E i →L[ℂ] E i)))
    have hd := displacement_product_le U x g h i
    linarith
  apply squeeze_zero (fun i => norm_nonneg _) hb
  simpa using ((hmul g h).mul_const C |>.add hg |>.add hh)

theorem almostInvariant_one {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) l (𝓝 0)) :
    AlmostInvariant l U x 1 := by
  apply squeeze_zero (fun i => norm_nonneg _) (fun i =>
    (ContinuousLinearMap.le_opNorm
      ((U 1 i : E i →L[ℂ] E i)-((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)) (x i)).trans
      (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _)))
  simpa using h1.mul_const C

theorem almostInvariant_inv {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    {g : Γ} (hg : AlmostInvariant l U x g) : AlmostInvariant l U x g⁻¹ := by
  have he := almostInvariant_one hx h1
  have hb (i : ι) : ‖U g⁻¹ i (x i)-x i‖ ≤
      ‖(U (g*g⁻¹) i : E i →L[ℂ] E i)-((U g i * U g⁻¹ i) : E i →L[ℂ] E i)‖ * C +
        ‖U 1 i (x i)-x i‖ + ‖U g i (x i)-x i‖ := by
    rw [← (U g i).norm_map (U g⁻¹ i (x i)-x i), map_sub]
    have ht := ContinuousLinearMap.le_opNorm
      ((U (g*g⁻¹) i : E i →L[ℂ] E i)-((U g i * U g⁻¹ i) : E i →L[ℂ] E i)) (x i)
    change ‖U (g*g⁻¹) i (x i)-U g i (U g⁻¹ i (x i))‖ ≤ _ at ht
    rw [mul_inv_cancel] at ht ⊢
    have ht' := ht.trans (mul_le_mul_of_nonneg_left (hx i) (norm_nonneg _))
    have htri := norm_sub_le_norm_sub_add_norm_sub (U g i (U g⁻¹ i (x i))) (U 1 i (x i)) (x i)
    have htri' := norm_sub_le_norm_sub_add_norm_sub (U g i (U g⁻¹ i (x i))) (x i) (U g i (x i))
    rw [norm_sub_rev (U g i (U g⁻¹ i (x i))) (U 1 i (x i))] at htri
    rw [norm_sub_rev (x i) (U g i (x i))] at htri'
    linarith
  apply squeeze_zero (fun i => norm_nonneg _) hb
  simpa using ((hmul g g⁻¹).mul_const C |>.add he |>.add hg)

/-- A fixed finite generating set controls every fixed group element. This
closure proof does not require relations at individual coordinates. -/
theorem almostInvariant_of_generators (S : Finset Γ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) {C : ℝ} (hx : ∀ i, ‖x i‖ ≤ C)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) l (𝓝 0))
    (hs : ∀ s ∈ S, AlmostInvariant l U x s) (g : Γ) : AlmostInvariant l U x g := by
  let K : Subgroup Γ := {
    carrier := {g | AlmostInvariant l U x g}
    one_mem' := almostInvariant_one hx h1
    mul_mem' := fun h k => almostInvariant_mul hx hmul h k
    inv_mem' := fun h => almostInvariant_inv hx h1 hmul h }
  have hK : Subgroup.closure (S : Set Γ) ≤ K := (Subgroup.closure_le K).mpr hs
  rw [hS] at hK
  exact hK (Subgroup.mem_top g)

end ApproxInvariant
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v w
section Energies
variable {ι : Type u} {Γ : Type v} {E : ι → Type w}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  (l : Filter ι) (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i) (x : ∀ i, E i)

theorem displacement_tendsto_of_energy
    (he : Tendsto (fun i => tupleEnergy S (fun g => U g i) (x i)) l (𝓝 0))
    (s : Γ) (hs : s ∈ S) : Tendsto (fun i => ‖U s i (x i)-x i‖) l (𝓝 0) := by
  have hb (i : ι) : ‖U s i (x i)-x i‖ ≤ Real.sqrt (tupleEnergy S (fun g => U g i) (x i)) := by
    apply (Real.le_sqrt (norm_nonneg _) (tupleEnergy_nonneg _ _ _)).mpr
    exact Finset.single_le_sum (f := fun g : Γ => ‖U g i (x i)-x i‖^2)
      (fun _ _ => sq_nonneg _) hs
  apply squeeze_zero (fun i => norm_nonneg _) hb
  simpa only [Real.sqrt_zero] using he.sqrt

end Energies

section Selection
variable {Γ : Type u} [Group Γ] {E : ℕ → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, Nontrivial (E i)]
  (ω : Ultrafilter ℕ) (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)

theorem free_le_atTop (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ)) :
    (ω : Filter ℕ) ≤ atTop := by
  rw [← Nat.cofinite_eq_atTop]
  exact le_cofinite_iff_compl_singleton_mem.mpr (fun i => (ω.compl_mem_iff_notMem).mpr (hω i))

omit [Group Γ] in
/-- Unit vectors with vanishing energy can be selected even while the Hilbert
spaces and their dimensions vary freely. -/
theorem exists_almost_invariant_vectors
    (hω : ∀ i : ℕ, ({i} : Set ℕ) ∉ (ω : Filter ℕ))
    (hd : Tendsto (fun i => bottomEnergy S (fun g => U g i)) (ω : Filter ℕ) (𝓝 0)) :
    ∃ x : ∀ i, E i, (∀ i, ‖x i‖ = 1) ∧
      Tendsto (fun i => tupleEnergy S (fun g => U g i) (x i)) (ω : Filter ℕ) (𝓝 0) := by
  have hp (i : ℕ) : (0 : ℝ) < 1/((i : ℝ)+1) := by positivity
  choose x hx he using (fun i => exists_energy_lt S (fun g => U g i) (hp i))
  refine ⟨x,hx,?_⟩
  apply squeeze_zero (fun i => tupleEnergy_nonneg _ _ _) (fun i => (he i).le)
  have ht : Tendsto (fun i : ℕ => (1 : ℝ)/((i : ℝ)+1)) (ω : Filter ℕ) (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.mono_left (free_le_atTop ω hω)
  simpa only [add_zero] using hd.add ht

/-- Matching below the Kazhdan threshold forces the bottom energies to zero;
this uses no common bound on the dimensions. -/
theorem bottom_tendsto_zero_of_small (κ a : ℝ)
    (hgap : HasKazhdanGap.{u,v} S κ) (ha : a < κ)
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hm : ∀ᶠ i in (ω : Filter ℕ), bottomEnergy S (fun g => U g i) < a) :
    Tendsto (fun i => bottomEnergy S (fun g => U g i)) (ω : Filter ℕ) (𝓝 0) := by
  have ht := HilbertUltraproduct.bottomEnergy_tendsto ω S U
  rcases HilbertUltraproduct.varying_gap ω S κ hgap U h1 hmul ht with hz | hg
  · rwa [hz] at ht
  · have hr : limUnder (ω : Filter ℕ) (fun i => bottomEnergy S (fun g => U g i)) ≤ a :=
      le_of_tendsto ht (hm.mono fun _ h => h.le)
    exact False.elim (ha.not_ge (hg.1.trans hr))
end Selection
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace TensorProduct
namespace NuclearUltrapower
universe u v
section TensorBounds
variable {E E' F F' : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [NormedAddCommGroup E'] [InnerProductSpace ℂ E']
  [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup F'] [InnerProductSpace ℂ F']

theorem tensorMapBetween_norm_le (U : E →L[ℂ] E') (V : F →L[ℂ] F') :
    ‖tensorMapBetween U V‖ ≤ ‖U‖ * ‖V‖ := by
  rw [tensorMapBetween, completed_norm]
  exact TensorProduct.norm_mapL_le _ _

theorem tensorMapBetween_sub_norm_le (U U' : E →L[ℂ] E') (V : F →ₗᵢ[ℂ] F') :
    ‖tensorMapBetween U V.toContinuousLinearMap - tensorMapBetween U' V.toContinuousLinearMap‖
      ≤ ‖U-U'‖ := by
  rw [← tensorMapBetween_sub_left]
  exact (tensorMapBetween_norm_le _ _).trans (by
    simpa using mul_le_mul_of_nonneg_left V.norm_toContinuousLinearMap_le (norm_nonneg (U-U')))

end TensorBounds
section Defects
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (u : Γ → unitary B)

theorem matchingTuple_mul_defect (π : FiniteUnitaryRep.{u,v} Γ) (g h : Γ) :
    ‖(matchingTuple ρ u π (g*h) : TensorHilbert E π →L[ℂ] TensorHilbert E π) -
      ((matchingTuple ρ u π g * matchingTuple ρ u π h) : TensorHilbert E π →L[ℂ] TensorHilbert E π)‖
    ≤ ‖(u (g*h) : B) - (u g : B)*(u h : B)‖ := by
  have ha : (π.action (g*h) : π →L[ℂ] π) =
      (π.action g : π →L[ℂ] π)*(π.action h : π →L[ℂ] π) := by
    rw [map_mul]; rfl
  change ‖completedTensorMap (ρ (u (g*h))) (π.action (g*h) : π →L[ℂ] π) -
      completedTensorMap (ρ (u g)) (π.action g : π →L[ℂ] π) *
        completedTensorMap (ρ (u h)) (π.action h : π →L[ℂ] π)‖ ≤ _
  rw [← completedTensorMap_mul, ← ha, ← map_mul]
  have hb := tensorMapBetween_sub_norm_le (ρ (u (g*h))) (ρ ((u g : B)*(u h : B)))
    (π.action (g*h)).toLinearIsometry
  exact hb.trans (by rw [← map_sub]; exact NonUnitalStarAlgHom.norm_apply_le ρ _)

end Defects
end NuclearUltrapower
end
end

end OAI
end

section
-- module Solutions.OAIQ019_Nuc.NuclearUltrapower_PullbackMatching
attribute [-instance] _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instInvolutiveStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instSeminormedRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarAddMonoidMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.GroupStarAlgebra.instStarRingMonoidAlgebraComplex_solutions _root_.OAI.NuclearUltrapower.UniversalCompletion.completionInvolutiveStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionNormedAlgebra _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStar _root_.OAI.NuclearUltrapower.UniversalCompletion.completionStarRing
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v
variable {Γ : Type u} [Group Γ] {E : ℕ → Type v}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)]
  [∀ i, Nontrivial (E i)]
  (ω : Ultrafilter ℕ) (S : Finset Γ) (U : Γ → ∀ i, E i ≃ₗᵢ[ℂ] E i)

theorem vectors_of_small_energies (κ a : ℝ) (hgap : HasKazhdanGap.{u,v} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : Tendsto (fun i => ‖(U 1 i : E i →L[ℂ] E i) -
      ((1 : E i ≃ₗᵢ[ℂ] E i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hmul : ∀ g h, Tendsto (fun i => ‖(U (g*h) i : E i →L[ℂ] E i) -
      ((U g i * U h i) : E i →L[ℂ] E i)‖) (ω : Filter ℕ) (𝓝 0))
    (hm : ∀ᶠ i in (ω : Filter ℕ), bottomEnergy S (fun g => U g i) < a) :
    ∃ x : ∀ i, E i, (∀ i, ‖x i‖ = 1) ∧ ∀ g, AlmostInvariant (ω : Filter ℕ) U x g := by
  have hb0 := bottom_tendsto_zero_of_small ω S U κ a hgap ha h1 hmul hm
  obtain ⟨ξ,hξ,he⟩ := exists_almost_invariant_vectors ω S U hω hb0
  refine ⟨ξ,hξ,fun g => ?_⟩
  apply almostInvariant_of_generators S hS (fun n => (hξ n).le) h1 hmul _ g
  intro s hs
  exact displacement_tendsto_of_energy (ω : Filter ℕ) S U ξ he s hs
end NuclearUltrapower
end
end

section

noncomputable section
open Filter
open scoped Topology InnerProductSpace
namespace NuclearUltrapower
universe u v
section MatchedVectors
variable {Γ : Type u} [Group Γ] {B E : Type v} [CStarAlgebra B]
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E] [Nontrivial E]
  (ρ : B →⋆ₐ[ℂ] (E →L[ℂ] E)) (S : Finset Γ) (u : Γ → ℕ → unitary B)
  (π : ℕ → FiniteUnitaryRep.{u,v} Γ) (ω : Ultrafilter ℕ)

omit [Nontrivial E] in
theorem matchingTuple_defects
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0)) (g h : Γ) :
    Tendsto (fun n => ‖(matchingTuple ρ (fun g => u g n) (π n) (g*h) :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((matchingTuple ρ (fun g => u g n) (π n) g * matchingTuple ρ (fun g => u g n) (π n) h) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))‖) (ω : Filter ℕ) (𝓝 0) := by
  have hb (n : ℕ) : 0 ≤ ‖(matchingTuple ρ (fun g => u g n) (π n) (g*h) :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((matchingTuple ρ (fun g => u g n) (π n) g * matchingTuple ρ (fun g => u g n) (π n) h) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))‖ := by
    exact norm_nonneg ((matchingTuple ρ (fun g => u g n) (π n) (g*h) :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((matchingTuple ρ (fun g => u g n) (π n) g * matchingTuple ρ (fun g => u g n) (π n) h) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)))
  exact squeeze_zero hb (fun n => matchingTuple_mul_defect ρ (fun g => u g n) (π n) g h) (hmul g h)

omit [Nontrivial E] in
theorem matchingTuple_identity (h1 : ∀ n, u 1 n = 1) :
    Tendsto (fun n => ‖(matchingTuple ρ (fun g => u g n) (π n) 1 :
      TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n)) -
      ((1 : TensorHilbert E (π n) ≃ₗᵢ[ℂ] TensorHilbert E (π n)) :
        TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))‖) (ω : Filter ℕ) (𝓝 0) := by
  have hz (n : ℕ) : matchingTuple ρ (fun g => u g n) (π n) 1 = 1 :=
    matchingTuple_one ρ (fun g => u g n) (π n) (h1 n)
  apply (tendsto_const_nhds (x := (0 : ℝ))).congr
  intro n
  rw [hz]
  rw [sub_self]
  exact (norm_zero (E := TensorHilbert E (π n) →L[ℂ] TensorHilbert E (π n))).symm

/-- A sequence of matched representations admits unit vectors invariant under
EVERY fixed group element in the ultralimit; dimensions are still unrestricted. -/
theorem matched_vectors_oai (κ a : ℝ) (hgap : HasKazhdanGap.{u,v} S κ)
    (hS : Subgroup.closure (S : Set Γ) = ⊤) (ha : a < κ)
    (hω : ∀ n : ℕ, ({n} : Set ℕ) ∉ (ω : Filter ℕ))
    (h1 : ∀ n, u 1 n = 1)
    (hmul : ∀ g h, Tendsto (fun n => ‖(u (g*h) n : B) - (u g n : B)*(u h n : B)‖)
      (ω : Filter ℕ) (𝓝 0))
    (hm : ∀ᶠ n in (ω : Filter ℕ), Matches ρ S (fun g => u g n) a (π n)) :
    ∃ ξ : ∀ n, TensorHilbert E (π n), (∀ n, ‖ξ n‖ = 1) ∧
      ∀ g, Tendsto (fun n => ‖matchingTuple ρ (fun g => u g n) (π n) g (ξ n) - ξ n‖)
        (ω : Filter ℕ) (𝓝 0) := by
  let U : Γ → ∀ n, TensorHilbert E (π n) ≃ₗᵢ[ℂ] TensorHilbert E (π n) :=
    fun g n => matchingTuple ρ (fun g => u g n) (π n) g
  have hi := matchingTuple_identity ρ u π ω h1
  have hd := matchingTuple_defects ρ u π ω hmul
  have hb : ∀ᶠ n in (ω : Filter ℕ), bottomEnergy S (fun g => U g n) < a := by
    filter_upwards [hm] with n hn
    obtain ⟨x,hx,he⟩ := hn
    exact (bottomEnergy_le S _ x hx).trans_lt he
  exact vectors_of_small_energies ω S U κ a hgap hS ha hω hi hd hb
end MatchedVectors
end NuclearUltrapower
end
end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.NuclearUltrapower.matched_vectors_oai.{u, v} := @OAI.NuclearUltrapower.matched_vectors_oai.{u, v}
