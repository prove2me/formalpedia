-- Prove2me | solution 1 for OAI.Paper256.BlockPencil.normalized_exists
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T20:22:31.792854+00:00
-- url     : https://prove2.me/submissions/57308ae8-30ff-468c-a778-855423d73f1f

-- Generated from openai/math@1581d4c lean/OAI/Analysis/HyperbolicCones/PencilRecovery.lean:L70-L93
-- (upload_full_project.md Phase 4): solution for node OAI.Paper256.BlockPencil.normalized_exists. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_HyperbolicCones
import Definitions.Def_OAI_Analysis_HyperbolicCones_Model
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_MatrixLinear
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilConjugation
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_RawBlocks
import Definitions.Def_OAI_Analysis_HyperbolicCones_KernelSpectrum
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitBasic
import Definitions.Def_OAI_Analysis_HyperbolicCones_SplitFrame
import Definitions.Def_OAI_Analysis_HyperbolicCones_CongruenceMaps
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockNormalization
import Definitions.Def_OAI_Analysis_HyperbolicCones_BlockReduction
import Definitions.Def_OAI_Analysis_HyperbolicCones_ScalingAlgebra
import Definitions.Def_OAI_Analysis_HyperbolicCones_FiniteTopology
import Definitions.Def_OAI_Analysis_HyperbolicCones_PencilLimit
import Theorems.Thm_OAI_Paper256_BlockPencil_scaled_posSemidef_iff
import Theorems.Thm_OAI_Paper256_FiniteMatrix_isOpen_posDef
import Theorems.Thm_OAI_Paper256_fromBlocks_add_lower_posDef
import Theorems.Thm_OAI_Paper256_isClosed_posSemidef

-- ---- from OAI.Analysis.HyperbolicCones.PencilOrder ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem posDef_of_scalar_lower_bound {n : ℕ} {X : Mat n ℝ} {c : ℝ}
    (hc : 0 < c) (hX : c • (1 : Mat n ℝ) ≤ X) : X.PosDef := by
  have h := (Matrix.PosDef.one.smul hc).add_posSemidef hX
  simpa only [add_sub_cancel] using h

theorem posDef_scalar_lower_bound {n : ℕ} (X : Mat n ℝ) (hX : X.PosDef) :
    ∃ c : ℝ, 0 < c ∧ c • (1 : Mat n ℝ) ≤ X := by
  classical
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · have := h
    exact ⟨1, zero_lt_one, (Subsingleton.elim _ _).le⟩
  · have := h
    have hh := (CFC.exists_pos_algebraMap_le_iff (a := X) hX.isHermitian).mpr
      (fun x hx => posDef_real_spectrum_positive hX hx)
    simpa only [Algebra.algebraMap_eq_smul_one] using hh

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PencilTopology ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u

namespace Paper256

theorem posSemidef_of_tendsto {α : Type u} {f : Filter α} [f.NeBot] {n : ℕ}
    {A : α → Sym n} {H : Sym n} (hA : Tendsto A f (𝓝 H))
    (h : ∀ᶠ x in f, (A x : Mat n ℝ).PosSemidef) : (H : Mat n ℝ).PosSemidef :=
  (isClosed_posSemidef n).mem_of_tendsto hA h

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PositiveMaps ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder

namespace Paper256

theorem positiveLinearMap_monotone {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym m, (X : Mat m ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (X Y : Sym m) (hXY : (X : Mat m ℝ) ≤ (Y : Mat m ℝ)) :
    (D X : Mat n ℝ) ≤ (D Y : Mat n ℝ) := by
  have h := hD (Y - X) hXY
  change ((D Y : Mat n ℝ) - (D X : Mat n ℝ)).PosSemidef
  simpa using h

theorem positive_unital_map_posDef {m n : ℕ} (D : Sym m →ₗ[ℝ] Sym n)
    (hD : ∀ X : Sym m, (X : Mat m ℝ).PosSemidef → (D X : Mat n ℝ).PosSemidef)
    (hI : D 1 = 1) (X : Sym m) (hX : (X : Mat m ℝ).PosDef) :
    (D X : Mat n ℝ).PosDef := by
  obtain ⟨c, hc, hcX⟩ := posDef_scalar_lower_bound (X : Mat m ℝ) hX
  apply posDef_of_scalar_lower_bound hc
  have h := positiveLinearMap_monotone D hD (c • 1) X hcX
  simpa [hI] using h

end Paper256

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.BlockReduction ----
namespace OAI

noncomputable section

open Set Matrix
open scoped Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem scaled_zero {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : P.scaled X Z y 0 = P.limit X Z y := by
  simp [scaled, limit]

end Paper256.BlockPencil

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.FiniteTopology ----
namespace OAI

noncomputable section

open Set Filter Matrix
open scoped Topology Matrix.Norms.L2Operator MatrixOrder

universe u v

namespace Paper256.FiniteMatrix

theorem isClosed_posSemidef (ι : Type u) [Fintype ι] [DecidableEq ι] : IsClosed {X : selfAdjoint (Matrix ι ι ℝ) | (X : Matrix ι ι ℝ).PosSemidef} := by
  have : FiniteDimensional ℝ (selfAdjoint (Matrix ι ι ℝ)) :=
    FiniteDimensional.finiteDimensional_submodule
      (selfAdjoint.submodule ℝ (Matrix ι ι ℝ))
  have heq : {X : selfAdjoint (Matrix ι ι ℝ) | (X : Matrix ι ι ℝ).PosSemidef} =
      ⋂ v : ι → ℝ, {X | 0 ≤ quadraticEvaluation v X} := by
    ext X
    simp only [mem_iInter, mem_ofPred_eq]
    constructor
    · intro h v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h.dotProduct_mulVec_nonneg v
    · intro h
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg X.property
      intro v
      simpa only [quadraticEvaluation, LinearMap.coe_mk, AddHom.coe_mk, star_trivial]
        using h v
  rw [heq]
  exact isClosed_iInter fun v => isClosed_le continuous_const
    (quadraticEvaluation v).continuous_of_finiteDimensional

theorem posSemidef_of_tendsto {α : Type u} {f : Filter α} [f.NeBot] {ι : Type v} [Fintype ι] [DecidableEq ι]
    {A : α → selfAdjoint (Matrix ι ι ℝ)} {H : selfAdjoint (Matrix ι ι ℝ)} (hA : Tendsto A f (𝓝 H))
    (h : ∀ᶠ x in f, (A x : Matrix ι ι ℝ).PosSemidef) : (H : Matrix ι ι ℝ).PosSemidef :=
  (isClosed_posSemidef ι).mem_of_tendsto hA h

end Paper256.FiniteMatrix

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PencilLimit ----
namespace OAI

noncomputable section

open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem scaled_polynomial {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (s : ℝ) :
    P.scaled X Z y s = P.limit X Z y +
      s • Matrix.fromBlocks (P.A y : Mat P.a ℝ) (P.C Z) (P.C Z)ᵀ (0 : Mat P.c ℝ) +
      s ^ 2 • Matrix.fromBlocks (P.F Z : Mat P.a ℝ) 0 0 (0 : Mat P.c ℝ) := by
  ext (i | i) (j | j) <;> simp [scaled, limit, Matrix.fromBlocks]

theorem scaled_continuous {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : Continuous (P.scaled X Z y) := by
  change Continuous (fun s : ℝ => P.scaled X Z y s)
  simp_rw [P.scaled_polynomial X Z y]
  fun_prop

theorem scaledSelfAdjoint_continuous {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) : Continuous (P.scaledSelfAdjoint X Z y) :=
  (P.scaled_continuous X Z y).subtype_mk _

theorem scaledSelfAdjoint_zero {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    P.scaledSelfAdjoint X Z y 0 = P.limitSelfAdjoint X Z y := by
  apply Subtype.ext
  exact P.scaled_zero X Z y

theorem scaled_tendsto {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) :
    Tendsto (P.scaledSelfAdjoint X Z y) (𝓝 0) (𝓝 (P.limitSelfAdjoint X Z y)) := by
  simpa only [P.scaledSelfAdjoint_zero X Z y] using
    (P.scaledSelfAdjoint_continuous X Z y).tendsto (0 : ℝ)

theorem limit_posSemidef_of_target {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef)
    (hZ : ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef) :
    (P.limit X Z y).PosSemidef := by
  have hsne : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs
    simpa using hs
  apply FiniteMatrix.posSemidef_of_tendsto (f := 𝓝[≠] (0 : ℝ))
    ((P.scaled_tendsto X Z y).mono_left inf_le_left)
  filter_upwards [hsne] with s hs
  exact (P.scaled_posSemidef_iff hSlice X Z y hX s hs).mpr hZ

end Paper256.BlockPencil

end

end OAI

-- ---- from OAI.Analysis.HyperbolicCones.PencilRecovery ----
namespace OAI

noncomputable section

open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator

namespace Paper256.BlockPencil

theorem limit_add_identity {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (δ : ℝ) :
    P.limit X (Z + δ • 1) y =
      Matrix.fromBlocks (P.D X : Mat P.a ℝ) (P.B y) (P.B y)ᵀ
        ((P.E Z : Mat P.c ℝ) + δ • 1) := by
  simp [limit, P.E_unital]

theorem limit_add_identity_posDef {K : Set Ambient} (P : BlockPencil K)
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef)
    (hM : (P.limit X Z y).PosSemidef) (δ : ℝ) (hδ : 0 < δ) :
    (P.limit X (Z + δ • 1) y).PosDef := by
  rw [P.limit_add_identity]
  exact fromBlocks_add_lower_posDef (P.D X) (P.E Z) (P.B y)
    (positive_unital_map_posDef P.D P.D_positive P.D_unital X hX) hM δ hδ

theorem target_of_limit_posSemidef {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef)
    (hM : (P.limit X Z y).PosSemidef) :
    ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
  have hregular (δ : ℝ) (hδ : 0 < δ) :
      (((Z + δ • 1 : Sym 4) : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef := by
    have hp := P.limit_add_identity_posDef X Z y hX hM δ hδ
    have hnb : {H : selfAdjoint (Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ) |
        (H : Matrix (Fin P.a ⊕ Fin P.c) (Fin P.a ⊕ Fin P.c) ℝ).PosDef} ∈
        𝓝 (P.limitSelfAdjoint X (Z + δ • 1) y) :=
      (FiniteMatrix.isOpen_posDef (Fin P.a ⊕ Fin P.c)).mem_nhds hp
    have he := (P.scaled_tendsto X (Z + δ • 1) y).eventually hnb
    have hsne : ∀ᶠ s : ℝ in 𝓝[≠] 0, s ≠ 0 := by
      filter_upwards [eventually_mem_nhdsWithin] with s hs
      simpa using hs
    have he' := (he.filter_mono nhdsWithin_le_nhds).and hsne
    obtain ⟨s, hps, hs⟩ := he'.exists
    exact (P.scaled_posSemidef_iff hSlice X (Z + δ • 1) y hX s hs).mp hps.posSemidef
  let T : Sym 4 := ⟨phi y (X : Mat 4 ℝ)⁻¹, phi_isHermitian y _ hX.inv.isHermitian⟩
  have hcont : Continuous (fun δ : ℝ => Z + δ • (1 : Sym 4) - T) := by fun_prop
  have hconv : Tendsto (fun δ : ℝ => Z + δ • (1 : Sym 4) - T)
      (𝓝[>] 0) (𝓝 (Z - T)) := by
    simpa using (hcont.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hevent : ∀ᶠ δ : ℝ in 𝓝[>] 0,
      ((Z + δ • 1 - T : Sym 4) : Mat 4 ℝ).PosSemidef := by
    filter_upwards [eventually_mem_nhdsWithin] with δ hδ
    simpa [T] using hregular δ hδ
  have hclosed := posSemidef_of_tendsto hconv hevent
  simpa [T] using hclosed

theorem limit_posSemidef_iff {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef))
    (X Z : Sym 4) (y : Fin 3 → ℝ) (hX : (X : Mat 4 ℝ).PosDef) :
    (P.limit X Z y).PosSemidef ↔
      ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef :=
  ⟨P.target_of_limit_posSemidef hSlice X Z y hX,
    P.limit_posSemidef_of_target hSlice X Z y hX⟩

theorem normalized_exists {K : Set Ambient} (P : BlockPencil K)
    (hSlice : ∀ (X Z : Sym 4) (y : Fin 3 → ℝ), (X : Mat 4 ℝ).PosDef →
      (((X, Z), y) ∈ K ↔ ((Z : Mat 4 ℝ) - phi y (X : Mat 4 ℝ)⁻¹).PosSemidef)) :
    Nonempty NormalizedPencil := by
  refine ⟨{
    a := P.a
    c := P.c
    a_pos := P.a_pos
    c_pos := P.c_pos
    D := P.D
    E := P.E
    B := P.B
    D_positive := P.D_positive
    E_positive := P.E_positive
    D_unital := P.D_unital
    E_unital := P.E_unital
    schur_equivalence := ?_
  }⟩
  intro X Z y hX
  have hD := positive_unital_map_posDef P.D P.D_positive P.D_unital X hX
  let := hD.isUnit.invertible
  rw [← P.limit_posSemidef_iff hSlice X Z y hX]
  simpa only [limit, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.PosDef.fromBlocks₁₁ (P.B y) (P.E Z : Mat P.c ℝ) hD

end Paper256.BlockPencil

end

end OAI

-- ---- platform node ----
open OAI OAI.Paper256 OAI.Paper256.BlockPencil
open Matrix Set Filter
open scoped Topology Matrix.Norms.L2Operator


theorem solution : type_of% @_root_.OAI.Paper256.BlockPencil.normalized_exists := @_root_.OAI.Paper256.BlockPencil.normalized_exists
