-- Prove2me | solution 1 for OAI.SharpLiebThirring.MatrixFlow.terminal_matching
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-23T14:03:22.89225+00:00
-- url     : https://prove2.me/submissions/e001517c-53e7-4018-8c93-786f80b8dbe8

import Mathlib
import Definitions.Def_OAIQWSLT000
import Theorems.Thm_OAI_SharpLiebThirring_CubeFlags_exists_terminal_zero_affine

section
-- module Solutions.OAIQW_LiebThirring.Compat
namespace OAI

/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
end OAICompat434

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.ActionPenalty
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u35

noncomputable section
open MeasureTheory
open scoped ENNReal Matrix.Norms.L2Operator
open Matrix
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder
noncomputable section
open Matrix Unitary MeasureTheory Set
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder CStarAlgebra
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open scoped NNReal


namespace SharpLiebThirring.PathProof
open Matrix
variable {N : ℕ}

/-- The initial row-sign orbit calculation, without assuming invertibility
of any later matching solution. -/
lemma lower_gram_diagonal {C : Matrix (Fin N) (Fin N) ℝ} (hC : LowerTriangular C)
    {d : Fin N → ℝ} (hd : ∀ i, 0 < d i) (hgram : C * C.transpose = diagonal d) :
    (∀ i j, i ≠ j → C i j = 0) ∧ (∀ i, C i i ^ 2 = d i) := by
  have hrow : ∀ i : Fin N, (∀ j, i ≠ j → C i j = 0) ∧ C i i ^ 2 = d i := by
    intro i
    induction i using WellFoundedLT.induction with
    | ind i ih =>
      have hoff : ∀ j, i ≠ j → C i j = 0 := by
        intro j hij
        rcases lt_or_gt_of_ne hij with hijlt | hjilt
        · exact hC i j hijlt
        · have hj := ih j hjilt
          have hne : C j j ≠ 0 := by
            intro he
            have := hd j
            rw [← hj.2, he] at this
            norm_num at this
          have hg := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i j) hgram
          have hsum : (C * C.transpose) i j = C i j * C j j := by
            simp only [mul_apply, transpose_apply]
            apply Finset.sum_eq_single j
            · intro b _ hbj
              rw [hj.1 b hbj.symm, mul_zero]
            · simp
          rw [hsum, diagonal_apply_ne _ hij] at hg
          exact (mul_eq_zero.mp hg).resolve_right hne
      refine ⟨hoff, ?_⟩
      have hg := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ A i i) hgram
      have hsum : (C * C.transpose) i i = C i i ^ 2 := by
        simp only [mul_apply, transpose_apply]
        rw [Finset.sum_eq_single i]
        · ring
        · intro b _ hbi
          rw [hoff b hbi.symm, zero_mul]
        · simp
      simpa only [hsum, diagonal_apply_eq] using hg
  exact ⟨fun i j hij ↦ (hrow i).1 j hij, fun i ↦ (hrow i).2⟩

lemma lower_gram_initial_orbit {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ)
    (hk : ∀ i, 0 < k i) {C : Matrix (Fin N) (Fin N) ℝ} (hC : LowerTriangular C)
    (hgram : C * C.transpose = diagonal (fun i ↦ 2 * ε * k i)) :
    ∃ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) ∧
      C = diagonal (fun i ↦ s i * Real.sqrt (2 * ε * k i)) := by
  have hpos (i : Fin N) : 0 < 2 * ε * k i := mul_pos (mul_pos (by norm_num) hε) (hk i)
  obtain ⟨hoff, hdiag⟩ := lower_gram_diagonal hC hpos hgram
  let s := fun i ↦ C i i / Real.sqrt (2 * ε * k i)
  refine ⟨s, ?_, ?_⟩
  · intro i
    have hsqrt : 0 < Real.sqrt (2 * ε * k i) := Real.sqrt_pos.2 (hpos i)
    have hs : s i ^ 2 = 1 := by
      dsimp [s]
      rw [div_pow, hdiag i, Real.sq_sqrt (hpos i).le]
      exact div_self (ne_of_gt (hpos i))
    rcases (sq_eq_one_iff).mp hs with h | h
    · exact Or.inl h
    · exact Or.inr h
  · ext i j
    by_cases hij : i = j
    · subst j
      rw [diagonal_apply_eq]
      dsimp [s]
      rw [div_mul_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2 (hpos i)))]
    · rw [diagonal_apply_ne _ hij, hoff i j hij]

end SharpLiebThirring.PathProof

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FlagGeometry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u39

noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags

lemma Signs.smul_real {n : ℕ} (s : Signs n) (x : Fin n → ℝ) (i : Fin n) :
    (s • x) i = if s.val i then -x i else x i := rfl

end SharpLiebThirring.CubeFlags

end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.EquivariantFlags
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u95 u96 u97 u98 u99 u100 u101 u102 u193 u194

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter


namespace SharpLiebThirring.CubeFlags
open Finset

lemma embed_spatial_of_time_zero {d : ℕ} (x : Fin (d + 1) → ℝ) (hx : x (Fin.last d) = 0) :
    embedSpatial (spatial x) = x := by
  change Fin.snoc (Fin.init x) 0 = x
  rw [← hx, Fin.snoc_init_self]

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.InitialOrbit
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u103 u104 u105 u106 u107 u108 u109 u110 u111 u112 u113 u114 u115

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
section
open Set Finset Filter


/-! Disjoint equivariant coordinate balls for the unique initial zero orbit. -/

open Set Finset
namespace SharpLiebThirring.PLParity
section OrbitBalls
attribute [local instance] Classical.propDecidable
variable {G : Type u103} {E : Type u104} [Group G] [MetricSpace E] [MulAction G E]
  [IsIsometricSMul G E]

omit [IsIsometricSMul G E] in
lemma orbit_separation [Fintype G] (p : E) (hp : ∀ g : G, g • p = p → g = 1) :
    ∃ R > 0, ∀ g k : G, g ≠ k → 8 * R < dist (g • p) (k • p) := by
  classical
  let d : G × G → ℝ := fun q ↦ if q.1 = q.2 then 1 else dist (q.1 • p) (q.2 • p)
  have hd (q : G × G) : 0 < d q := by
    dsimp [d]
    split_ifs with he
    · norm_num
    · apply dist_pos.mpr
      intro hh
      have hx : (q.2⁻¹ * q.1) • p = p := by rw [mul_smul, hh, inv_smul_smul]
      exact he (inv_mul_eq_one.mp (hp _ hx)).symm
  have hn : (Finset.univ : Finset (G × G)).Nonempty := ⟨(1,1), Finset.mem_univ _⟩
  let b := Finset.univ.inf' hn d
  have hb : 0 < b := (Finset.lt_inf'_iff _).mpr (fun q _ ↦ hd q)
  refine ⟨b / 16, by positivity, ?_⟩
  intro g k hgk
  have hle : b ≤ d (g,k) := Finset.inf'_le _ (Finset.mem_univ _)
  dsimp [d] at hle
  rw [ite_eq_right hgk] at hle
  linarith

variable (p : E) (R : ℝ)

omit [IsIsometricSMul G E] in
lemma ballLabel_dist {x : E} (hx : x ∈ orbitBall (G := G) p R) :
    dist x (ballLabel (G := G) p R x • p) < R := by
  rw [ballLabel, dif_pos hx]
  exact hx.choose_spec

variable (hR : 0 < R) (hsep : ∀ g k : G, g ≠ k → 8 * R < dist (g • p) (k • p))

include hR hsep in
omit [IsIsometricSMul G E] in
lemma ballLabel_eq {x : E} {g : G} (hx : dist x (g • p) < R) :
    ballLabel (G := G) p R x = g := by
  by_contra hn
  have hl := ballLabel_dist p R (show x ∈ orbitBall (G := G) p R from ⟨g,hx⟩)
  have hd := dist_triangle (ballLabel (G := G) p R x • p) x (g • p)
  rw [dist_comm (ballLabel (G := G) p R x • p) x] at hd
  have hs := hsep _ _ hn
  linarith

end OrbitBalls
end SharpLiebThirring.PLParity

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma Signs.smul_time_zero {d : ℕ} (s : Signs (d + 1)) (x : Fin (d + 1) → ℝ)
    (hx : x (Fin.last d) = 0) : (s • x) (Fin.last d) = 0 := by
  simp only [Signs.smul_real, hx, neg_zero, ite_self]

end SharpLiebThirring.CubeFlags

end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FreeLocus
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u116 u117 u118 u119 u120 u121 u122 u123 u124 u125 u126 u127 u128 u129 u130 u131 u132 u133 u134 u135

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

section


/-! Analytic compactness and free-locus facts for the PL continuation proof. -/

open Set Finset
namespace SharpLiebThirring.PLParity

section FreeLocus
variable {G : Type u120} {E : Type u121} [Group G] [MulAction G E]

lemma freeLocus_smul (g : G) {x : E} (hx : x ∈ freeLocus (G := G)) :
    g • x ∈ freeLocus (G := G) := by
  intro s hs
  have hfix : (g⁻¹ * s * g) • x = x := by
    rw [mul_smul, mul_smul, hs, inv_smul_smul]
  have he := hx _ hfix
  have hh := congrArg (fun a : G ↦ g * a * g⁻¹) he
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hh

variable [TopologicalSpace E] [T2Space E] [ContinuousConstSMul G E] [Finite G]

lemma isOpen_freeLocus : IsOpen (freeLocus (G := G) (E := E)) := by
  classical
  have hset : freeLocus (G := G) (E := E) = ⋂ g : {g : G // g ≠ 1}, {x | g.val • x ≠ x} := by
    ext x
    simp only [freeLocus, mem_ofPred_eq, mem_iInter]
    constructor
    · intro h ⟨g, hg⟩ he
      exact hg (h g he)
    · intro h g hg
      by_contra hn
      exact h ⟨g, hn⟩ hg
  rw [hset]
  apply isOpen_iInter_of_finite
  intro g
  exact (isClosed_eq (continuous_const_smul g.val) continuous_id).isOpen_compl

end FreeLocus
end SharpLiebThirring.PLParity

end

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.BoundaryParity
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u136 u137 u138 u139 u140 u141 u142

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma dist_spatial_le {d : ℕ} (x y : Fin (d + 1) → ℝ) :
    dist (spatial x) (spatial y) ≤ dist x y := by
  rw [dist_pi_le_iff dist_nonneg]
  intro i
  exact dist_le_pi_dist x y i.castSucc

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.Continuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u143 u144 u145 u146 u147

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

lemma radialCut_nonneg (R t : ℝ) : 0 ≤ radialCut R t := le_max_left _ _
lemma radialCut_le_one (R t : ℝ) : radialCut R t ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)
lemma radialCut_eq_zero (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : R ≤ t) : radialCut R t = 0 := by
  classical
  apply max_eq_left
  apply (min_le_right _ _).trans
  have hd : 2 ≤ 2*t/R := (le_div_iff₀ hR).mpr (by linarith)
  linarith
lemma radialCut_eq_one (R : ℝ) (hR : 0 < R) {t : ℝ} (ht : t ≤ R/2) : radialCut R t = 1 := by
  classical
  have hd : 2*t/R ≤ 1 := (div_le_iff₀ hR).mpr (by linarith)
  simp only [radialCut, min_eq_left (by linarith : 1 ≤ 2 - 2*t/R), max_eq_right zero_le_one]
lemma continuous_radialCut (R : ℝ) : Continuous (radialCut R) := by
  classical
  unfold radialCut
  fun_prop

section Flatten
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u143} [NormedAddCommGroup V] [NormedSpace ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin d → ℝ) (R : ℝ) (f : (Fin (d + 1) → ℝ) → V)

lemma localAffine_smul (s g : H) (x : Fin (d + 1) → ℝ) :
    localAffine H ρ L p (g*s) (g • x) = ρ g (localAffine H ρ L p s x) := by
  classical
  simp only [localAffine,mul_inv_rev,mul_smul,inv_smul_smul,map_mul,LinearEquiv.mul_apply]

lemma continuous_localAffine [FiniteDimensional ℝ V] (s : H) : Continuous (localAffine H ρ L p s) := by
  classical
  unfold localAffine
  exact (ρ s).toContinuousLinearEquiv.continuous.comp
    (L.toContinuousLinearEquiv.continuous.comp
      ((spatial.continuous_of_finiteDimensional.comp (continuous_const_smul s⁻¹)).sub continuous_const))

lemma continuous_flattenInitial [FiniteDimensional ℝ V] (hf : Continuous f) : Continuous (flattenInitial H ρ L p R f) := by
  classical
  apply hf.add
  apply continuous_finsetSum
  intro s _
  exact ((continuous_radialCut R).comp (continuous_id.dist continuous_const)).smul
    ((continuous_localAffine H ρ L p s).sub hf)

lemma flattenInitial_equivariant (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (g : H) (x : Fin (d + 1) → ℝ) :
    flattenInitial H ρ L p R f (g • x) = ρ g (flattenInitial H ρ L p R f x) := by
  classical
  have ht (s : H) : flattenTerm H ρ L p R f (g*s) (g • x) =
      ρ g (flattenTerm H ρ L p R f s x) := by
    simp only [flattenTerm,mul_smul,dist_smul,localAffine_smul,hfe,map_smul,map_sub]
  have he := Fintype.sum_equiv (Equiv.mulLeft g)
    (fun s : H ↦ ρ g (flattenTerm H ρ L p R f s x))
    (fun s : H ↦ flattenTerm H ρ L p R f s (g • x)) (fun s ↦ (ht s).symm)
  simp only [flattenInitial,hfe,map_add,map_sum]
  exact congrArg (ρ g (f x) + ·) he.symm

lemma flattenInitial_eq_self {x : Fin (d + 1) → ℝ} (hR : 0 < R)
    (hx : x ∉ orbitBall (G := H) (embedSpatial p) R) :
    flattenInitial H ρ L p R f x = f x := by
  classical
  have ht : ∀ s : H, R ≤ dist x (s • embedSpatial p) :=
    fun s ↦ le_of_not_gt (fun hs ↦ hx ⟨s,hs⟩)
  unfold flattenInitial
  have hz : ∀ s : H, flattenTerm H ρ L p R f s x = 0 := by
    intro s
    unfold flattenTerm
    rw [radialCut_eq_zero R hR (ht s),zero_smul]
  simp only [hz,Finset.sum_const_zero,add_zero]

lemma flattenInitial_in_ball (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    {x : Fin (d + 1) → ℝ} (hx : x ∈ orbitBall (G := H) (embedSpatial p) R) :
    flattenInitial H ρ L p R f x = f x +
      radialCut R (dist x (ballLabel (G := H) (embedSpatial p) R x • embedSpatial p)) •
        (affineOrbitModel H ρ L (embedSpatial p) R p x - f x) := by
  classical
  let s := ballLabel (G := H) (embedSpatial p) R x
  have hs := ballLabel_dist (embedSpatial p) R hx
  have ht (k : H) (hk : k ≠ s) : flattenTerm H ρ L p R f k x = 0 := by
    have hd := hsep s k hk.symm
    have he := dist_triangle (s • embedSpatial p) x (k • embedSpatial p)
    rw [dist_comm (s • embedSpatial p) x] at he
    have hdk : R ≤ dist x (k • embedSpatial p) := by
      change dist x (s • embedSpatial p) < R at hs
      linarith
    simp only [flattenTerm,radialCut_eq_zero R hR hdk,zero_smul]
  have hsum : ∑ k : H, flattenTerm H ρ L p R f k x = flattenTerm H ρ L p R f s x := by
    apply Finset.sum_eq_single s
    · intro k _ hk
      exact ht k hk
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  rw [flattenInitial,hsum]
  rfl

lemma flattenInitial_inner (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    {x : Fin (d + 1) → ℝ} (hx : x ∈ orbitBall (G := H) (embedSpatial p) (R/2)) :
    flattenInitial H ρ L p R f x = affineOrbitModel H ρ L (embedSpatial p) (R/2) p x := by
  classical
  obtain ⟨s,hs⟩ := hx
  have hsR : dist x (s • embedSpatial p) < R := by linarith
  have hlR := ballLabel_eq (embedSpatial p) R hR hsep hsR
  have hsep' : ∀ g k : H, g ≠ k → 8 * (R/2) < dist (g • embedSpatial p) (k • embedSpatial p) := by
    intro g k hgk
    linarith [hsep g k hgk]
  have hlhalf := ballLabel_eq (embedSpatial p) (R/2) (by positivity) hsep' hs
  rw [flattenInitial_in_ball H ρ L p R f hR hsep ⟨s,hsR⟩,hlR,
    radialCut_eq_one R hR hs.le,one_smul]
  simp only [affineOrbitModel,hlR,hlhalf]
  abel

lemma affineOrbitModel_zero_bottom
    {x : Fin (d + 1) → ℝ} (ht : x (Fin.last d) = 0)
    (hz : affineOrbitModel H ρ L (embedSpatial p) R p x = 0) :
    ∃ s : H, s • embedSpatial p = x := by
  classical
  let s := ballLabel (G := H) (embedSpatial p) R x
  have hu : spatial (s⁻¹ • x) - p = 0 := by
    apply L.injective
    apply (ρ s).injective
    simpa only [affineOrbitModel,map_zero,s] using hz
  have he := embed_spatial_of_time_zero (s⁻¹ • x) ((s⁻¹).val.smul_time_zero x ht)
  rw [sub_eq_zero.mp hu] at he
  refine ⟨s,?_⟩
  rw [he,smul_inv_smul]

lemma flattenInitial_zero_bottom (hR : 0 < R)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (herr : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      ‖f x - affineOrbitModel H ρ L (embedSpatial p) R p x‖ ≤
        ‖affineOrbitModel H ρ L (embedSpatial p) R p x‖ / 2)
    {x : Fin (d + 1) → ℝ} (ht : x (Fin.last d) = 0)
    (hz : flattenInitial H ρ L p R f x = 0) : ∃ s : H, s • embedSpatial p = x := by
  classical
  by_cases hx : x ∈ orbitBall (G := H) (embedSpatial p) R
  · let m := affineOrbitModel H ρ L (embedSpatial p) R p x
    let a := radialCut R (dist x (ballLabel (G := H) (embedSpatial p) R x • embedSpatial p))
    have hz' : f x + a • (m - f x) = 0 := by
      rw [flattenInitial_in_ball H ρ L p R f hR hsep hx] at hz
      exact hz
    have ha : 0 ≤ a := radialCut_nonneg _ _
    have ha1 : a ≤ 1 := radialCut_le_one _ _
    have he : f x + a • (m - f x) = m + (1-a) • (f x-m) := by
      rw [sub_smul,one_smul,smul_sub,smul_sub]
      abel
    rw [he] at hz'
    have hn : ‖m‖ ≤ ‖f x-m‖ := by
      have hm : m = -((1-a) • (f x-m)) := eq_neg_of_add_eq_zero_left hz'
      have heN := congrArg norm hm
      rw [norm_neg,norm_smul,Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ 1-a)] at heN
      nlinarith [norm_nonneg (f x-m)]
    have hm0 : m = 0 := norm_eq_zero.mp (by linarith [herr x ht hx,norm_nonneg m])
    exact affineOrbitModel_zero_bottom H ρ L p R ht hm0
  · exact hz0 x ht ((flattenInitial_eq_self H ρ L p R f hR hx).symm.trans hz)

lemma flattenInitial_final (hR : 0 < R) (hR1 : R ≤ 1) {x : Fin (d + 1) → ℝ} (ht : x (Fin.last d) = 1) :
    flattenInitial H ρ L p R f x = f x := by
  classical
  apply flattenInitial_eq_self H ρ L p R f hR
  rintro ⟨s,hs⟩
  have hd := dist_le_pi_dist x (s • embedSpatial p) (Fin.last d)
  have hst : (s • embedSpatial p) (Fin.last d) = 0 :=
    s.val.smul_time_zero _ (by change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) p 0 (Fin.last d) = 0; simp only [Fin.snoc_last])
  rw [ht,hst] at hd
  norm_num at hd
  linarith

end Flatten
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity
section FlattenCompact
variable {d : ℕ} (H : Subgroup (Signs (d + 1)))
variable {V : Type u144} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
variable (p : Fin d → ℝ) (R : ℝ) (f : (Fin (d + 1) → ℝ) → V)

lemma compact_zeros_flattenInitial (hR : 0 < R) (hf : Continuous f)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0}) :
    IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ flattenInitial H ρ L p R f x = 0} := by
  classical
  have hc := hK.union (isCompact_iUnion
    (fun s : H ↦ isCompact_closedBall (s • embedSpatial p) R))
  apply hc.of_isClosed_subset
  · exact (isClosed_Icc.preimage (continuous_apply _)).inter
      (isClosed_eq (continuous_flattenInitial H ρ L p R f hf) continuous_const)
  · intro x hx
    by_cases hb : x ∈ orbitBall (G := H) (embedSpatial p) R
    · obtain ⟨s,hs⟩ := hb
      exact Or.inr (Set.mem_iUnion.mpr ⟨s,hs.le⟩)
    · exact Or.inl ⟨hx.1,(flattenInitial_eq_self H ρ L p R f hR hb).symm.trans hx.2⟩

/-- A simple initial zero need only agree with its invertible linearization up
to a relative error of one half. Compactly supported flattening turns this
into the affine continuation theorem, without adding any new final zeros. -/
theorem exists_terminal_zero_local
    (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (hR : 0 < R) (hR1 : R ≤ 1)
    (hsep : ∀ g k : H, g ≠ k → 8 * R < dist (g • embedSpatial p) (k • embedSpatial p))
    (hball : orbitBall (G := H) (embedSpatial p) R ⊆ freeLocus (G := H))
    (hf : Continuous f) (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (herr : ∀ x, x (Fin.last d) = 0 → x ∈ orbitBall (G := H) (embedSpatial p) R →
      ‖f x - affineOrbitModel H ρ L (embedSpatial p) R p x‖ ≤
        ‖affineOrbitModel H ρ L (embedSpatial p) R p x‖ / 2)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0})
    (hfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → f x = 0 →
      ∀ s : H, s • x = x → s = 1) :
    ∃ x : Fin (d + 1) → ℝ, x (Fin.last d) = 1 ∧ f x = 0 := by
  classical
  let g := flattenInitial H ρ L p R f
  have hsep' : ∀ s t : H, s ≠ t → 8 * (R/2) < dist (s • embedSpatial p) (t • embedSpatial p) := by
    intro s t hst
    linarith [hsep s t hst]
  have hgfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → g x = 0 →
      ∀ s : H, s • x = x → s = 1 := by
    intro x hx hz s hs
    by_cases hb : x ∈ orbitBall (G := H) (embedSpatial p) R
    · exact hball hb s hs
    · apply hfree x hx _ s hs
      exact (flattenInitial_eq_self H ρ L p R f hR hb).symm.trans hz
  obtain ⟨x,hxt,hxg⟩ := exists_terminal_zero_affine H hHt ρ L hρ p (R/2) (by positivity)
    hsep' g (continuous_flattenInitial H ρ L p R f hf).continuousOn
    (flattenInitial_equivariant H ρ L p R f hfe)
    (fun x _ hx ↦ flattenInitial_inner H ρ L p R f hR hsep hx)
    (fun x ht hz ↦ flattenInitial_zero_bottom H ρ L p R f hR hsep hz0 herr ht hz)
    (compact_zeros_flattenInitial H ρ L p R f hR hf hK) hgfree
  refine ⟨x,hxt,?_⟩
  exact (flattenInitial_final H ρ L p R f hR hR1 hxt).symm.trans hxg

end FlattenCompact
end SharpLiebThirring.CubeFlags

namespace SharpLiebThirring.CubeFlags
lemma hasFDerivAt_relative_error {E : Type u145} {V : Type u146}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    (f : E → V) (p : E) (L : E ≃L[ℝ] V) (hf0 : f p = 0)
    (hd : HasFDerivAt f L.toContinuousLinearMap p) :
    ∃ δ > 0, ∀ u : E, dist u p < δ → ‖f u - L (u-p)‖ ≤ ‖L (u-p)‖ / 2 := by
  let M := ‖L.symm.toContinuousLinearMap‖
  have hM : 0 ≤ M := norm_nonneg _
  let c := 1 / (2*(M+1))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcM : c*M ≤ 1/2 := by
    dsimp [c]
    rw [one_div_mul_eq_div, div_le_iff₀ (by positivity : 0 < 2*(M+1))]
    linarith
  obtain ⟨δ,hδ,he⟩ := Metric.eventually_nhds_iff.mp (hd.isLittleO.def hc)
  refine ⟨δ,hδ,fun u hu ↦ ?_⟩
  have hsmall : ‖f u - L (u-p)‖ ≤ c * ‖u-p‖ := by simpa only [hf0,sub_zero,ContinuousLinearEquiv.coe_coe] using he hu
  have hnorm : ‖u-p‖ ≤ M * ‖L (u-p)‖ := by
    have h := L.symm.toContinuousLinearMap.le_opNorm (L (u-p))
    simpa only [ContinuousLinearEquiv.coe_coe,L.symm_apply_apply] using h
  calc
    ‖f u - L (u-p)‖ ≤ c*‖u-p‖ := hsmall
    _ ≤ c*(M*‖L (u-p)‖) := mul_le_mul_of_nonneg_left hnorm hc.le
    _ = (c*M)*‖L (u-p)‖ := by ring
    _ ≤ (1/2)*‖L (u-p)‖ := mul_le_mul_of_nonneg_right hcM (norm_nonneg _)
    _ = ‖L (u-p)‖/2 := by ring
end SharpLiebThirring.CubeFlags


namespace SharpLiebThirring.CubeFlags
open Finset SharpLiebThirring.PLParity

/-- A continuous equivariant homotopy with compact free zero set and one simple
initial zero orbit must have a terminal zero. No smoothness is required away
from the distinguished initial point. -/
theorem exists_terminal_zero_simple {d : ℕ}
    (H : Subgroup (Signs (d + 1))) (hHt : ∀ s : H, s.val.val (Fin.last d) = false)
    {V : Type u147} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (ρ : H →* (V ≃ₗ[ℝ] V)) (L : (Fin d → ℝ) ≃ₗ[ℝ] V)
    (hρ : ∀ s : H, ∀ v : V, ‖ρ s v‖ = ‖v‖)
    (p : Fin d → ℝ) (f : (Fin (d + 1) → ℝ) → V)
    (hf : Continuous f) (hfe : ∀ s : H, ∀ x, f (s • x) = ρ s (f x))
    (hp0 : f (embedSpatial p) = 0)
    (hd : HasFDerivAt (fun u : Fin d → ℝ ↦ f (embedSpatial u))
      L.toContinuousLinearEquiv.toContinuousLinearMap p)
    (hz0 : ∀ x, x (Fin.last d) = 0 → f x = 0 → ∃ s : H, s • embedSpatial p = x)
    (hK : IsCompact {x | x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 ∧ f x = 0})
    (hfree : ∀ x, x (Fin.last d) ∈ Set.Icc (0 : ℝ) 1 → f x = 0 →
      ∀ s : H, s • x = x → s = 1) :
    ∃ x : Fin (d + 1) → ℝ, x (Fin.last d) = 1 ∧ f x = 0 := by
  classical
  have ht0 : (embedSpatial p) (Fin.last d) = 0 := by
    change Fin.snoc (α := fun _ : Fin (d + 1) ↦ ℝ) p 0 (Fin.last d) = 0
    simp only [Fin.snoc_last]
  have hpFree : embedSpatial p ∈ freeLocus (G := H) :=
    hfree _ (by rw [ht0]; exact ⟨le_refl _,zero_le_one⟩) hp0
  obtain ⟨R₁,hR₁,hsep⟩ := orbit_separation (G := H) (embedSpatial p) hpFree
  obtain ⟨R₂,hR₂,hball⟩ := Metric.isOpen_iff.mp (isOpen_freeLocus (G := H)) _ hpFree
  obtain ⟨δ,hδ,herr⟩ := hasFDerivAt_relative_error (fun u : Fin d → ℝ ↦ f (embedSpatial u))
    p L.toContinuousLinearEquiv hp0 hd
  let R := min 1 (min R₁ (min R₂ δ))
  have hR : 0 < R := lt_min zero_lt_one (lt_min hR₁ (lt_min hR₂ hδ))
  have hR1 : R ≤ 1 := min_le_left _ _
  have hRR₁ : R ≤ R₁ := (min_le_right _ _).trans (min_le_left _ _)
  have hRR₂ : R ≤ R₂ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRδ : R ≤ δ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hsep' : ∀ s t : H, s ≠ t → 8*R < dist (s • embedSpatial p) (t • embedSpatial p) := by
    intro s t hst
    linarith [hsep s t hst]
  have hball' : orbitBall (G := H) (embedSpatial p) R ⊆ freeLocus (G := H) := by
    rintro x ⟨s,hs⟩
    have hx : dist (s⁻¹ • x) (embedSpatial p) < R₂ := by
      have he := dist_smul s⁻¹ x (s • embedSpatial p)
      rw [inv_smul_smul] at he
      rw [he]
      exact hs.trans_le hRR₂
    have hb := freeLocus_smul s (hball hx)
    simpa only [smul_inv_smul] using hb
  apply exists_terminal_zero_local H ρ L p R f hHt hρ hR hR1 hsep' hball' hf hfe hz0
  · intro x ht hx
    let s := ballLabel (G := H) (embedSpatial p) R x
    let y := s⁻¹ • x
    let u := spatial y
    have htY : y (Fin.last d) = 0 := (s⁻¹).val.smul_time_zero x ht
    have hY : embedSpatial u = y := embed_spatial_of_time_zero y htY
    have hdist : dist u p < δ := by
      have hs := ballLabel_dist (embedSpatial p) R hx
      have he := dist_smul s⁻¹ x (s • embedSpatial p)
      rw [inv_smul_smul] at he
      have hdu := dist_spatial_le y (embedSpatial p)
      rw [spatial_embed] at hdu
      exact hdu.trans_lt ((he ▸ hs).trans_le hRδ)
    have her := herr u hdist
    have hfx : f x = ρ s (f (embedSpatial u)) := by
      rw [hY,← hfe,smul_inv_smul]
    change ‖f x - ρ s (L (u-p))‖ ≤ ‖ρ s (L (u-p))‖ / 2
    rw [hfx,← map_sub,hρ,hρ]
    exact her
  · exact hK
  · exact hfree

end SharpLiebThirring.CubeFlags

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.RowSigns
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

lemma rowSubgroup_time {N : ℕ} (s : rowSubgroup N) : s.val.val (Fin.last (lowerDim N)) = false := s.prop.1
lemma rowSubgroup_coord {N : ℕ} (s : rowSubgroup N) (a : Fin (lowerDim N)) :
    s.val.val a.castSucc = rowBool s (rowIndex a) := s.prop.2 a

lemma rowBool_injective {N : ℕ} : Function.Injective (rowBool (N := N)) := by
  intro s t h
  apply Subtype.ext
  apply Signs.ext
  funext a
  refine Fin.lastCases ?_ (fun b ↦ ?_) a
  · rw [rowSubgroup_time,rowSubgroup_time]
  · rw [rowSubgroup_coord,rowSubgroup_coord,h]

lemma signValue_cases (b : Bool) : signValue b = 1 ∨ signValue b = -1 := by cases b <;> simp [signValue]
lemma signValue_xor (b c : Bool) : signValue (xor b c) = signValue b * signValue c := by
  cases b <;> cases c <;> norm_num [signValue]
lemma signValue_smul (b : Bool) (x : ℝ) : (if b then -x else x) = signValue b * x := by
  cases b <;> simp [signValue]

lemma conjugateRepresentation_norm {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N) → ℝ) :
    ‖conjugateRepresentation N s x‖ = ‖x‖ := (conjugateSigns s).linearIsometry.norm_map x
lemma conjugateRepresentation_apply {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N) → ℝ)
    (a : Fin (lowerDim N)) :
    conjugateRepresentation N s x a = signValue (rowBool s (rowIndex a)) * x a * signValue (rowBool s (colIndex a)) := by
  change (if xor (rowBool s (rowIndex a)) (rowBool s (colIndex a)) then -x a else x a) = _
  rw [signValue_smul,signValue_xor]
  ring

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

lemma continuous_matrixCoords {N : ℕ} : Continuous (matrixCoords (N := N)) := by
  apply continuous_pi
  intro a
  exact (continuous_apply _).comp (continuous_apply _)
lemma matrixCoords_eq_zero {N : ℕ} {A : Matrix (Fin N) (Fin N) ℝ}
    (hA : A.IsHermitian) (h : matrixCoords A = 0) : A = 0 := by
  have hl (i j : Fin N) (hji : j ≤ i) : A i j = 0 := by
    have he := congrFun h (indexEquiv N ⟨(i,j),hji⟩)
    simpa [matrixCoords,rowIndex,colIndex] using he
  ext i j
  rcases le_total j i with hj | hi
  · exact hl i j hj
  · have hs : A j i = A i j := by simpa using congrArg (fun B ↦ B i j) hA
    exact hs.symm.trans (hl j i hi)

lemma lowerEntry_apply {N : ℕ} (i j : Fin N) (x : Fin (lowerDim N) → ℝ) :
    lowerEntry i j x = (lowerOfCoords x).val i j := by
  dsimp [lowerEntry,lowerOfCoords]
  split_ifs <;> rfl
lemma lowerEntry_diagonal {N : ℕ} (i j : Fin N) (c : Fin N → ℝ) :
    lowerEntry i j (diagonalPoint c) = diagonal c i j := by
  rw [lowerEntry_apply,lowerOfCoords_diagonalPoint]
  rfl

lemma initialMap_hasFDerivAt {N : ℕ} (β : ℝ) (hβ : β ≠ 0) (k c : Fin N → ℝ) (hc : ∀ i, 0 < c i) :
    HasFDerivAt (initialMap β k)
      (initialLinearEquiv β hβ c hc).toContinuousLinearEquiv.toContinuousLinearMap (diagonalPoint c) := by
  classical
  let p := diagonalPoint c
  let D := fun a : Fin (lowerDim N) ↦ -(β • ∑ m : Fin N,
    ((lowerEntry (rowIndex a) m p) • lowerEntry (colIndex a) m +
      (lowerEntry (colIndex a) m p) • lowerEntry (rowIndex a) m))
  have hd : HasFDerivAt (initialMap β k) (ContinuousLinearMap.pi D) p := by
    apply hasFDerivAt_pi.mpr
    intro a
    have hsum := HasFDerivAt.fun_sum (x := p) (u := Finset.univ) (fun m _ ↦
      (lowerEntry (rowIndex a) m).hasFDerivAt.mul (lowerEntry (colIndex a) m).hasFDerivAt)
    convert (hsum.const_mul β).const_sub ((2 • diagonal k) (rowIndex a) (colIndex a)) using 1
    · funext x
      simp only [initialMap,matrixCoords,Matrix.sub_apply,Matrix.smul_apply,Matrix.mul_apply,
        transpose_apply,smul_eq_mul,Pi.mul_apply,lowerEntry_apply]
  have hD : ContinuousLinearMap.pi D =
      (initialLinearEquiv β hβ c hc).toContinuousLinearEquiv.toContinuousLinearMap := by
    ext x a
    simp only [ContinuousLinearMap.pi_apply,ContinuousLinearEquiv.coe_coe]
    change D a x = jacobianWeight β c a * x a
    dsimp [D,p]
    simp only [_root_.neg_apply,_root_.smul_apply,_root_.sum_apply,
      _root_.add_apply,smul_eq_mul,lowerEntry_diagonal,Finset.sum_add_distrib]
    rw [Finset.sum_eq_single (rowIndex a),Finset.sum_eq_single (colIndex a)]
    · simp only [diagonal_apply_eq,lowerEntry_apply]
      have ha : (lowerOfCoords x).val (rowIndex a) (colIndex a) = x a :=
        congrFun (lowerCoords_lowerOfCoords x) a
      rw [ha]
      by_cases he : rowIndex a = colIndex a
      · rw [he] at ha ⊢
        rw [ha]
        simp only [jacobianWeight,he,↓reduceIte]
        ring
      · have hlt : colIndex a < rowIndex a := lt_of_le_of_ne (colIndex_le_rowIndex a) (Ne.symm he)
        rw [(lowerOfCoords x).prop _ _ hlt]
        simp only [jacobianWeight,he,↓reduceIte]
        ring
    · intro m _ hm
      rw [diagonal_apply_ne _ hm.symm,zero_mul]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
    · intro m _ hm
      rw [diagonal_apply_ne _ hm.symm,zero_mul]
    · simp only [Finset.mem_univ,not_true_eq_false,false_implies]
  rwa [hD] at hd

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

lemma continuous_clampTime : Continuous clampTime := continuous_const.max (continuous_id.min continuous_const)
lemma clampTime_mem (t : ℝ) : clampTime t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _,max_le zero_le_one (min_le_right _ _)⟩
lemma clampTime_eq {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : clampTime t = t := by
  rw [clampTime,min_eq_left ht.2,max_eq_right ht.1]
@[simp] lemma clampTime_zero : clampTime 0 = 0 := clampTime_eq ⟨le_refl _,zero_le_one⟩
@[simp] lemma clampTime_one : clampTime 1 = 1 := clampTime_eq ⟨zero_le_one,le_refl _⟩

lemma continuous_homotopyCoords {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hΦ : ContinuousOn (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1) (Set.univ ×ˢ Set.Icc 0 1)) :
    Continuous (homotopyCoords Φ) := by
  apply continuous_matrixCoords.comp
  exact hΦ.comp_continuous
    ((continuous_lowerOfCoords.comp spatial.continuous_of_finiteDimensional).prodMk
      (continuous_clampTime.comp (continuous_apply _)))
    (fun x ↦ ⟨Set.mem_univ _,clampTime_mem _⟩)

lemma lowerOfCoords_smul {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N + 1) → ℝ) :
    lowerOfCoords (spatial (s • x)) = rowSign (fun i ↦ signValue (rowBool s i)) (lowerOfCoords (spatial x)) := by
  apply Subtype.ext
  funext i j
  by_cases hji : j ≤ i
  · change (if h : j ≤ i then spatial (s • x) (indexEquiv N ⟨(i,j),h⟩) else 0) = _
    simp only [hji,↓reduceDIte]
    change (s.val • x) (indexEquiv N ⟨(i,j),hji⟩).castSucc =
      signValue (rowBool s i) * (if h : j ≤ i then spatial x (indexEquiv N ⟨(i,j),h⟩) else 0)
    rw [Signs.smul_real,rowSubgroup_coord]
    have hr : rowIndex (indexEquiv N ⟨(i,j),hji⟩) = i := by simp [rowIndex]
    rw [hr,signValue_smul]
    simp only [hji,↓reduceDIte]
    rfl
  · change (if h : j ≤ i then spatial (s • x) (indexEquiv N ⟨(i,j),h⟩) else 0) = _
    simp only [hji,↓reduceDIte,rowSign,lowerOfCoords,mul_zero]

lemma time_smul {N : ℕ} (s : rowSubgroup N) (x : Fin (lowerDim N + 1) → ℝ) :
    (s • x) (Fin.last (lowerDim N)) = x (Fin.last (lowerDim N)) := by
  change (s.val • x) _ = _
  rw [Signs.smul_real,rowSubgroup_time]
  rfl

lemma homotopyCoords_equivariant {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (he : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, ∀ s : Fin N → ℝ,
      (∀ i, s i = 1 ∨ s i = -1) → Φ θ (rowSign s C) = signConjugate s (Φ θ C))
    (s : rowSubgroup N) (x : Fin (lowerDim N + 1) → ℝ) :
    homotopyCoords Φ (s • x) = conjugateRepresentation N s (homotopyCoords Φ x) := by
  unfold homotopyCoords
  rw [time_smul,lowerOfCoords_smul,he _ (clampTime_mem _) _ _ (fun _ ↦ signValue_cases _)]
  ext a
  rw [conjugateRepresentation_apply]
  rfl

lemma homotopyCoords_eq_zero {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    {x : Fin (lowerDim N + 1) → ℝ} (ht : x (Fin.last (lowerDim N)) ∈ Set.Icc (0 : ℝ) 1) :
    homotopyCoords Φ x = 0 ↔ Φ (x (Fin.last (lowerDim N))) (lowerOfCoords (spatial x)) = 0 := by
  rw [homotopyCoords,clampTime_eq ht]
  constructor
  · exact matrixCoords_eq_zero (hs _ ht _)
  · intro h
    rw [h]
    rfl

lemma compact_homotopyCoords_zeros {N : ℕ} (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    (hK : IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0}) :
    IsCompact {x : Fin (lowerDim N + 1) → ℝ | x (Fin.last (lowerDim N)) ∈ Set.Icc (0 : ℝ) 1 ∧ homotopyCoords Φ x = 0} := by
  have hh := (spaceTimeHomeomorph N).isCompact_preimage.mpr hK
  convert hh using 1
  ext x
  change (_ ∧ _) ↔ (_ ∧ _)
  constructor
  · rintro ⟨ht,hx⟩
    exact ⟨ht,(homotopyCoords_eq_zero Φ hs ht).mp hx⟩
  · rintro ⟨ht,hx⟩
    exact ⟨ht,(homotopyCoords_eq_zero Φ hs ht).mpr hx⟩

lemma rowAction_free {N : ℕ} (x : Fin (lowerDim N + 1) → ℝ)
    (hx : NonzeroRows (lowerOfCoords (spatial x)))
    (s : rowSubgroup N) (he : s • x = x) : s = 1 := by
  apply rowBool_injective
  funext i
  rw [rowBool_one]
  obtain ⟨j,hj⟩ := hx i
  have heC := congrArg (fun y ↦ (lowerOfCoords (spatial y)).val i j) he
  rw [lowerOfCoords_smul] at heC
  change signValue (rowBool s i) * (lowerOfCoords (spatial x)).val i j = (lowerOfCoords (spatial x)).val i j at heC
  rcases Bool.eq_false_or_eq_true (rowBool s i) with hb | hb
  · rw [hb,signValue_true,neg_one_mul] at heC
    exact False.elim (hj (by linarith))
  · exact hb

lemma homotopyCoords_initial {N : ℕ} (ε : ℝ) (k : Fin N → ℝ)
    (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (h0 : ∀ C, Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose))
    (u : Fin (lowerDim N) → ℝ) :
    homotopyCoords Φ (embedSpatial u) = initialMap ε⁻¹ k u := by
  unfold homotopyCoords
  have ht : embedSpatial u (Fin.last (lowerDim N)) = 0 := by
    change Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) u 0 (Fin.last (lowerDim N)) = 0
    exact Fin.snoc_last _ _
  rw [ht,clampTime_zero,spatial_embed,h0]
  rfl

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

lemma initial_matrix_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) :
    2 • diagonal k - ε⁻¹ • ((diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))).val *
      (diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))).val.transpose) = 0 := by
  change 2 • diagonal k - ε⁻¹ • (diagonal (fun i ↦ Real.sqrt (2*ε*k i)) *
    (diagonal (fun i ↦ Real.sqrt (2*ε*k i))).transpose) = 0
  rw [diagonal_transpose,diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.sub_apply,Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul,Matrix.zero_apply]
    rw [← sq,Real.sq_sqrt (le_of_lt (mul_pos (mul_pos (by norm_num) hε) (hk i)))]
    field_simp [ne_of_gt hε]
    ring
  · simp only [Matrix.sub_apply,Matrix.smul_apply,diagonal_apply_ne _ hij,smul_eq_mul,smul_zero,mul_zero,sub_self,Matrix.zero_apply]

lemma gram_of_initial_zero {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (C : LowerSpace N)
    (h : 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose) = 0) :
    C.val * C.val.transpose = diagonal (fun i ↦ 2*ε*k i) := by
  have he : ε • (2 • diagonal k) = C.val * C.val.transpose := by
    have he := congrArg (fun A : Matrix (Fin N) (Fin N) ℝ ↦ ε • A) (sub_eq_zero.mp h)
    simpa only [smul_smul,mul_inv_cancel₀ (ne_of_gt hε),one_smul] using he
  rw [← he]
  ext i j
  by_cases hij : i = j
  · subst j
    simp only [Matrix.smul_apply,diagonal_apply_eq,smul_eq_mul]
    ring
  · simp only [Matrix.smul_apply,diagonal_apply_ne _ hij,smul_eq_mul,smul_zero,mul_zero]

lemma homotopyCoords_initial_orbit {N : ℕ} {ε : ℝ} (hε : 0 < ε) (k : Fin N → ℝ) (hk : ∀ i, 0 < k i)
    (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    (h0 : ∀ C, Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose))
    (x : Fin (lowerDim N + 1) → ℝ) (ht : x (Fin.last (lowerDim N)) = 0)
    (hx : homotopyCoords Φ x = 0) :
    ∃ s : rowSubgroup N, s • embedSpatial (diagonalPoint (fun i ↦ Real.sqrt (2*ε*k i))) = x := by
  classical
  let C := lowerOfCoords (spatial x)
  have hΦ : Φ 0 C = 0 := by
    have hh := (homotopyCoords_eq_zero Φ hs (by rw [ht]; exact ⟨le_refl _,zero_le_one⟩)).mp hx
    simpa only [ht] using hh
  rw [h0] at hΦ
  obtain ⟨s,hsign,hC⟩ := PathProof.lower_gram_initial_orbit hε k hk C.prop (gram_of_initial_zero hε k C hΦ)
  let b : Fin N → Bool := fun i ↦ decide (s i = -1)
  have hb (i : Fin N) : signValue (b i) = s i := by
    rcases hsign i with hi | hi
    · norm_num [b,hi,signValue]
    · norm_num [b,hi,signValue]
  have hrow : rowSign (fun i ↦ signValue (rowBool (rowElement b) i))
      (diagonalLower (fun i ↦ Real.sqrt (2*ε*k i))) = C := by
    apply Subtype.ext
    change (fun i j ↦ signValue (rowBool (rowElement b) i) * diagonal (fun i ↦ Real.sqrt (2*ε*k i)) i j) = C.val
    rw [hC]
    ext i j
    rw [rowBool_rowElement,hb]
    by_cases hij : i = j
    · subst j
      simp only [diagonal_apply_eq]
    · simp only [diagonal_apply_ne _ hij,mul_zero]
  refine ⟨rowElement b,?_⟩
  apply (spaceTimeHomeomorph N).injective
  apply Prod.ext
  · change lowerOfCoords (spatial ((rowElement b) • embedSpatial (diagonalPoint _))) = C
    rw [lowerOfCoords_smul,spatial_embed,lowerOfCoords_diagonalPoint,hrow]
  · change ((rowElement b) • embedSpatial (diagonalPoint (fun i ↦ Real.sqrt (2*ε*k i)))) (Fin.last (lowerDim N)) = x (Fin.last (lowerDim N))
    rw [time_smul,ht]
    change Fin.snoc (α := fun _ : Fin (lowerDim N + 1) ↦ ℝ) _ 0 (Fin.last (lowerDim N)) = 0
    exact Fin.snoc_last _ _

end SharpLiebThirring.PathTopology
namespace SharpLiebThirring.PathTopology
open Matrix SharpLiebThirring.CubeFlags SharpLiebThirring.ContinuationGap

/-- Row-sign continuation. Rank
deficiency is allowed throughout; only zero rows at matching solutions are excluded. -/
theorem equivariant_continuation (N : ℕ) (ε : ℝ) (k : Fin N → ℝ)
    (hε : 0 < ε) (hk : ∀ i, 0 < k i)
    (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hΦ : ContinuousOn (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1) (Set.univ ×ˢ Set.Icc 0 1))
    (hs : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, (Φ θ C).IsHermitian)
    (he : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, ∀ s : Fin N → ℝ,
      (∀ i, s i = 1 ∨ s i = -1) → Φ θ (rowSign s C) = signConjugate s (Φ θ C))
    (h0 : ∀ C, Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val * C.val.transpose))
    (hK : IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Set.Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0})
    (hn : ∀ θ ∈ Set.Icc (0 : ℝ) 1, ∀ C, Φ θ C = 0 → NonzeroRows C) :
    ∃ C, Φ 1 C = 0 := by
  let c := fun i ↦ Real.sqrt (2*ε*k i)
  have hc (i : Fin N) : 0 < c i := Real.sqrt_pos.mpr (mul_pos (mul_pos (by norm_num) hε) (hk i))
  have hβ : ε⁻¹ ≠ 0 := inv_ne_zero (ne_of_gt hε)
  let L := initialLinearEquiv ε⁻¹ hβ c hc
  let p := diagonalPoint c
  let f := homotopyCoords Φ
  have hp0 : f (embedSpatial p) = 0 := by
    change homotopyCoords Φ (embedSpatial p) = 0
    rw [homotopyCoords_initial ε k Φ h0]
    dsimp only [initialMap, p]
    rw [lowerOfCoords_diagonalPoint]
    rw [initial_matrix_zero hε k hk]
    rfl
  have hd : HasFDerivAt (fun u ↦ f (embedSpatial u)) L.toContinuousLinearEquiv.toContinuousLinearMap p := by
    have hh : (fun u ↦ f (embedSpatial u)) = initialMap ε⁻¹ k :=
      funext (homotopyCoords_initial ε k Φ h0)
    rw [hh]
    exact initialMap_hasFDerivAt ε⁻¹ hβ k c hc
  obtain ⟨x,ht,hx⟩ := exists_terminal_zero_simple (rowSubgroup N) rowSubgroup_time
    (conjugateRepresentation N) L conjugateRepresentation_norm p f
    (continuous_homotopyCoords Φ hΦ) (homotopyCoords_equivariant Φ he) hp0 hd
    (homotopyCoords_initial_orbit hε k hk Φ hs h0)
    (compact_homotopyCoords_zeros Φ hs hK)
    (fun x ht hx ↦ rowAction_free x
      (hn _ ht _ ((homotopyCoords_eq_zero Φ hs ht).mp hx)))
  refine ⟨lowerOfCoords (spatial x),?_⟩
  have hh := (homotopyCoords_eq_zero Φ hs (by rw [ht]; exact ⟨zero_le_one,le_refl _⟩)).mp hx
  simpa only [ht] using hh

end SharpLiebThirring.PathTopology

end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.MatrixFlow
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe u148 u149 u150 u151 u152 u153 u154 u155 u156 u157

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset

noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
namespace SharpLiebThirring.ODEProof

/-- Bounded globally Lipschitz fields have solutions on the entire prescribed
compact interval. There is no restriction on the length of the interval. -/
lemma bounded_ode_exists {E : Type u148} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {l r : ℝ} (hlr : l ≤ r) (x₀ : E) (f : ℝ → E → E) (K L : ℝ≥0)
    (hK : ∀ t ∈ Icc l r, LipschitzWith K (f t))
    (hc : ∀ x, ContinuousOn (fun t ↦ f t x) (Icc l r))
    (hL : ∀ t ∈ Icc l r, ∀ x, ‖f t x‖ ≤ L) :
    ∃ x : ℝ → E, x l = x₀ ∧ ∀ t ∈ Icc l r, HasDerivWithinAt x (f t (x t)) (Icc l r) t := by
  let a : ℝ≥0 := L * ⟨r-l,sub_nonneg.mpr hlr⟩
  have hp : IsPicardLindelof f ⟨l,⟨le_refl _,hlr⟩⟩ x₀ a 0 L K :=
    { lipschitzOnWith := fun t ht ↦ (hK t ht).lipschitzOnWith
      continuousOn := fun x _ ↦ hc x
      norm_le := fun t ht x _ ↦ hL t ht x
      mul_max_le := by
        change (L : ℝ) * max (r-l) (l-l) ≤ (a : ℝ) - 0
        simp only [sub_self,max_eq_left (sub_nonneg.mpr hlr),sub_zero]
        rfl }
  exact hp.exists_eq_forall_mem_Icc_hasDerivWithinAt₀

lemma derivative_right_of_Icc {E : Type u149} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r t : ℝ} {f : ℝ → E} {v : E} (ht : t ∈ Ico l r)
    (h : HasDerivWithinAt f v (Icc l r) t) : HasDerivWithinAt f v (Ici t) t :=
  h.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE_of_mem ht)

/-- Uniform perturbation estimate for solutions, including both endpoint times. -/
lemma bounded_ode_perturbation {E : Type u150} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r : ℝ} {f g : ℝ → E → E} {x y : ℝ → E} {K : ℝ≥0} {η : ℝ}
    (hK : ∀ t, LipschitzWith K (g t))
    (hx : ∀ t ∈ Icc l r, HasDerivWithinAt x (f t (x t)) (Icc l r) t)
    (hy : ∀ t ∈ Icc l r, HasDerivWithinAt y (g t (y t)) (Icc l r) t)
    (hxy : x l = y l)
    (herr : ∀ t ∈ Icc l r, ∀ z, dist (f t z) (g t z) ≤ η) :
    ∀ t ∈ Icc l r, dist (x t) (y t) ≤ gronwallBound 0 K η (t-l) := by
  have hh := dist_le_of_approx_trajectories_ODE hK
    (HasDerivWithinAt.continuousOn hx)
    (fun t ht ↦ derivative_right_of_Icc ht (hx t (mem_Icc_of_Ico ht)))
    (fun t ht ↦ herr t (mem_Icc_of_Ico ht) (x t))
    (HasDerivWithinAt.continuousOn hy)
    (fun t ht ↦ derivative_right_of_Icc ht (hy t (mem_Icc_of_Ico ht)))
    (fun t _ ↦ (dist_self _).le)
    (show dist (x l) (y l) ≤ 0 by rw [hxy,dist_self])
  simpa only [add_zero] using hh

lemma bounded_ode_unique {E : Type u151} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r : ℝ} {f : ℝ → E → E} {x y : ℝ → E} {K : ℝ≥0}
    (hK : ∀ t, LipschitzWith K (f t))
    (hx : ∀ t ∈ Icc l r, HasDerivWithinAt x (f t (x t)) (Icc l r) t)
    (hy : ∀ t ∈ Icc l r, HasDerivWithinAt y (f t (y t)) (Icc l r) t)
    (hxy : x l = y l) : EqOn x y (Icc l r) := by
  intro t ht
  apply dist_le_zero.mp
  have hh := bounded_ode_perturbation hK hx hy hxy (fun _ _ _ ↦ (dist_self _).le) t ht
  simpa only [gronwallBound_ε0_δ0] using hh

end SharpLiebThirring.ODEProof
namespace SharpLiebThirring.ODEProof
open Set Metric Filter

/-- Continuous parameter dependence, uniform even when the evaluation time varies. -/
lemma continuous_solution_family {E : Type u152} {P : Type u153} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace P] {l r : ℝ} {f : P → ℝ → E → E} {x : P → ℝ → E}
    (K : P → ℝ≥0) (η : P → P → ℝ)
    (hK : ∀ p t, LipschitzWith (K p) (f p t))
    (hx : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (x p) (f p t (x p t)) (Icc l r) t)
    (hinit : ∀ p q, x p l = x q l)
    (hη : ∀ p, Continuous (fun q ↦ η q p)) (hη0 : ∀ p, η p p = 0)
    (hηpos : ∀ p q, 0 ≤ η p q)
    (herr : ∀ p q t, t ∈ Icc l r → ∀ z, dist (f p t z) (f q t z) ≤ η p q) :
    Continuous (fun z : P × Icc l r ↦ x z.1 z.2) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hb : ∀ w : P × Icc l r,
      dist (x w.1 w.2) (x z.1 z.2) ≤
        gronwallBound 0 (K z.1) (η w.1 z.1) (r-l) + dist (x z.1 w.2) (x z.1 z.2) := by
    intro w
    apply (dist_triangle _ (x z.1 w.2) _).trans
    apply add_le_add _ (le_refl _)
    exact (bounded_ode_perturbation (hK z.1) (hx w.1) (hx z.1) (hinit w.1 z.1)
      (herr w.1 z.1) w.2 w.2.prop).trans
      (gronwallBound_mono (by positivity) (hηpos w.1 z.1) (K z.1).prop
        (sub_le_sub_right w.2.prop.2 l))
  apply squeeze_zero' (Eventually.of_forall (fun _ ↦ dist_nonneg)) (Eventually.of_forall hb)
  have hfirst : Tendsto (fun w : P × Icc l r ↦ gronwallBound 0 (K z.1) (η w.1 z.1) (r-l))
      (𝓝 z) (𝓝 0) := by
    have hh := ((gronwallBound_continuous_ε 0 (K z.1) (r-l)).comp
      ((hη z.1).comp continuous_fst)).continuousAt (x := z)
    simpa only [ContinuousAt,Function.comp_def,hη0,gronwallBound_ε0_δ0] using hh
  have hc : Continuous (fun t : Icc l r ↦ x z.1 t) :=
    (HasDerivWithinAt.continuousOn (hx z.1)).domRestrict
  have hsecond : Tendsto (fun w : P × Icc l r ↦ dist (x z.1 w.2) (x z.1 z.2))
      (𝓝 z) (𝓝 0) := by
    have hh := ((hc.comp continuous_snd).dist (continuous_const (y := x z.1 z.2))).continuousAt (x := z)
    simpa only [ContinuousAt,Function.comp_def,dist_self] using hh
  simpa only [add_zero] using hfirst.add hsecond

/-- Ready-to-use parameterized affine forcing in a bounded Lipschitz field. -/
lemma affine_forcing_exists_family {E : Type u154} {P : Type u155} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace P] {l r : ℝ} (hlr : l ≤ r) (x₀ : E)
    (M : E → E) (K B : ℝ≥0) (hK : LipschitzWith K M) (hB : ∀ x, ‖M x‖ ≤ B)
    (a : P → ℝ) (ha : Continuous a) (v : P → C(Icc l r,E)) (hv : Continuous v) :
    ∃ x : P → ℝ → E, (∀ p, x p l = x₀) ∧
      (∀ p t (ht : t ∈ Icc l r), HasDerivWithinAt (x p)
        (a p • M (x p t) + v p ⟨t,ht⟩) (Icc l r) t) ∧
      Continuous (fun z : P × Icc l r ↦ x z.1 z.2) := by
  let V : P → ℝ → E := fun p t ↦ if ht : t ∈ Icc l r then v p ⟨t,ht⟩ else 0
  have hV (p : P) : ContinuousOn (V p) (Icc l r) := by
    rw [continuousOn_iff_continuous_domRestrict]
    convert (v p).continuous using 1
    funext t
    simp only [Set.domRestrict,V,dite_eq_left t.prop]
  have hVnorm (p : P) (t : ℝ) (ht : t ∈ Icc l r) : ‖V p t‖ ≤ ‖v p‖ := by
    simpa only [V,dite_eq_left ht] using (v p).norm_coe_le_norm ⟨t,ht⟩
  let f := fun p t y ↦ a p • M y + V p t
  have hLip (p : P) (t : ℝ) : LipschitzWith (‖a p‖₊ * K) (f p t) := by
    apply lipschitzWith_iff_norm_sub_le.mpr
    intro y z
    simp only [f,add_sub_add_right_eq_sub,← smul_sub,norm_smul,NNReal.coe_mul,coe_nnnorm]
    exact (mul_le_mul_of_nonneg_left (lipschitzWith_iff_norm_sub_le.mp hK y z)
      (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm
  have hex (p : P) : ∃ x : ℝ → E, x l = x₀ ∧
      ∀ t ∈ Icc l r, HasDerivWithinAt x (f p t (x t)) (Icc l r) t := by
    apply bounded_ode_exists hlr x₀ (f p) (‖a p‖₊ * K) (‖a p‖₊ * B + ‖v p‖₊)
      (fun t _ ↦ hLip p t) (fun y ↦ continuousOn_const.add (hV p))
    intro t ht y
    calc ‖f p t y‖ ≤ ‖a p • M y‖ + ‖V p t‖ := norm_add_le _ _
      _ ≤ ‖a p‖ * B + ‖v p‖ := by rw [norm_smul]; gcongr; exact hB _; exact hVnorm p t ht
      _ = _ := by rfl
  choose x hxi hxd using hex
  refine ⟨x,hxi,?_,?_⟩
  · intro p t ht
    simpa only [f,V,dite_eq_left ht] using hxd p t ht
  · let η := fun p q ↦ ‖a p - a q‖ * B + ‖v p - v q‖
    apply continuous_solution_family (fun p ↦ ‖a p‖₊ * K) η hLip hxd
      (fun p q ↦ (hxi p).trans (hxi q).symm)
      (fun p ↦ (ha.sub continuous_const).norm.mul_const _ |>.add (hv.sub continuous_const).norm)
      (fun p ↦ by simp [η]) (fun p q ↦ by dsimp [η]; positivity)
    intro p q t ht y
    have hdiff : f p t y - f q t y = (a p-a q) • M y + (V p t - V q t) := by
      dsimp [f]; module
    rw [dist_eq_norm,hdiff]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · rw [norm_smul]; exact mul_le_mul_of_nonneg_left (hB _) (norm_nonneg _)
    · simpa only [V,dite_eq_left ht,ContinuousMap.sub_apply] using
        (v p-v q).norm_coe_le_norm ⟨t,ht⟩

end SharpLiebThirring.ODEProof
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology
namespace SharpLiebThirring.MatrixFlow
lemma symConj_diag {N : ℕ} (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (k : Fin N → ℝ) : symConj s (symDiag k) = symDiag k := by
  apply Subtype.ext
  ext i j
  by_cases hij : i=j
  · subst j
    change s i * diagonal k i i * s i = diagonal k i i
    rw [diagonal_apply_eq]
    rcases hs i with h|h <;> rw [h] <;> ring
  · change s i * diagonal k i j * s j = diagonal k i j
    simp only [diagonal_apply_ne _ hij,mul_zero,zero_mul]
lemma symConj_outer {N : ℕ} (s a : Fin N → ℝ) :
    symConj s (symOuter a) = symOuter (fun i ↦ s i * a i) := by
  apply Subtype.ext; ext i j; dsimp [symOuter,symConj,vecMulVec]; ring

lemma zero_row_sign {N : ℕ} (i : Fin N) :
    ∀ j : Fin N, (if j=i then (-1 : ℝ) else 1) = 1 ∨ (if j=i then (-1 : ℝ) else 1) = -1 := by
  intro j; split_ifs <;> simp
lemma fixed_reflection_offdiag {N : ℕ} (i : Fin N) (A : Sym N)
    (h : symConj (fun j ↦ if j=i then -1 else 1) A = A) (j : Fin N) (hij : i ≠ j) :
    A.val i j = 0 := by
  have hh := congrArg (fun B : Sym N ↦ B.val i j) h
  simp only [symConj_apply,ite_true,ite_eq_right (Ne.symm hij),neg_mul,one_mul,mul_one] at hh
  linarith

lemma matrix_norm_entry {N : ℕ} (B : Matrix (Fin N) (Fin N) ℝ) (i j : Fin N) :
    |B i j| ≤ ‖B‖ := by
  let T : EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) (n := Fin N) B
  have h := T.le_opNorm (toLp 2 (Pi.single j (1 : ℝ)))
  have hh := PiLp.norm_apply_le (T (toLp 2 (Pi.single j (1 : ℝ)))) i
  simpa [T, Matrix.toEuclideanCLM_toLp, Matrix.l2_opNorm_toEuclideanCLM] using hh.trans h

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open ODEProof Set Matrix
open scoped Topology
variable {N : ℕ}

lemma continuous_matrixForcing (ε : ℝ) {l r : ℝ} (u : ℝ → Fin N → ℝ)
    (hu : ContinuousOn u (Icc l r)) : Continuous (matrixForcing ε u hu) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun z : Matrix (Fin N) (Fin N) ℝ × Icc l r ↦
    -ε⁻¹ • symOuter (z.1 *ᵥ u z.2))
  have hu' := hu.domRestrict.comp (continuous_snd (X := Matrix (Fin N) (Fin N) ℝ))
  exact (continuous_symOuter.comp (continuous_fst.matrix_mulVec hu')).const_smul (-ε⁻¹)

lemma flowRhs_lipschitz (ε : ℝ) (M : Sym N → Sym N) {L : ℝ≥0}
    (hL : LipschitzWith L M) (u : ℝ → Fin N → ℝ)
    (p : Matrix (Fin N) (Fin N) ℝ × ℝ) (t : ℝ) :
    LipschitzWith (‖ε⁻¹*p.2‖₊ * L) (flowRhs ε M u p t) := by
  apply lipschitzWith_iff_norm_sub_le.mpr
  intro A B
  simp only [flowRhs,sub_sub_sub_cancel_right,← smul_sub,norm_smul,
    NNReal.coe_mul,coe_nnnorm]
  exact (mul_le_mul_of_nonneg_left (lipschitzWith_iff_norm_sub_le.mp hL A B)
    (norm_nonneg _)).trans_eq (mul_assoc _ _ _).symm

lemma matrix_flow_exists {l r : ℝ} (hlr : l ≤ r) (ε : ℝ) (k : Fin N → ℝ)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (M : Sym N → Sym N) (L B : ℝ≥0) (hL : LipschitzWith L M) (hB : ∀ A, ‖M A‖ ≤ B) :
    ∃ X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N,
      (∀ p, X p l = symDiag k) ∧
      (∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t) ∧
      Continuous (fun z : (Matrix (Fin N) (Fin N) ℝ × ℝ) × Icc l r ↦ X z.1 z.2) := by
  obtain ⟨X,hXi,hXd,hXc⟩ := affine_forcing_exists_family hlr (symDiag k) M L B hL hB
    (fun p : Matrix (Fin N) (Fin N) ℝ × ℝ ↦ ε⁻¹*p.2) (by fun_prop)
    (fun p ↦ matrixForcing ε u hu p.1) ((continuous_matrixForcing ε u hu).comp continuous_fst)
  refine ⟨X,hXi,?_,hXc⟩
  intro p t ht
  simpa only [flowRhs,matrixForcing,ContinuousMap.coe_mk,neg_smul,sub_eq_add_neg] using hXd p t ht

lemma matrix_rowSign_mulVec (s : Fin N → ℝ) (C : Matrix (Fin N) (Fin N) ℝ)
    (u : Fin N → ℝ) : (fun i j ↦ s i * C i j) *ᵥ u = fun i ↦ s i * (C *ᵥ u) i := by
  ext i
  simp only [mulVec,dotProduct,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma flowRhs_equivariant (ε : ℝ) (M : Sym N → Sym N) (u : ℝ → Fin N → ℝ)
    (s : Fin N → ℝ) (hM : ∀ A, M (symConj s A) = symConj s (M A))
    (C : Matrix (Fin N) (Fin N) ℝ) (θ t : ℝ) (A : Sym N) :
    flowRhs ε M u (fun i j ↦ s i * C i j,θ) t (symConj s A) =
      symConj s (flowRhs ε M u (C,θ) t A) := by
  simp only [flowRhs,hM,map_sub,map_smul,matrix_rowSign_mulVec,symConj_outer]

lemma matrix_flow_equivariant {l r ε : ℝ} {M : Sym N → Sym N} {L : ℝ≥0}
    (hL : LipschitzWith L M) (k : Fin N → ℝ) (u : ℝ → Fin N → ℝ)
    (X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N)
    (hXi : ∀ p, X p l = symDiag k)
    (hXd : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t)
    (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (hM : ∀ A, M (symConj s A) = symConj s (M A))
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) :
    EqOn (X (fun i j ↦ s i*C i j,θ)) (fun t ↦ symConj s (X (C,θ) t)) (Icc l r) := by
  apply bounded_ode_unique (fun t ↦ flowRhs_lipschitz ε M hL u (fun i j ↦ s i*C i j,θ) t)
    (hXd _) _ (by rw [hXi,hXi,symConj_diag s hs])
  intro t ht
  have hh := (symConj s).hasFDerivAt.comp_hasDerivWithinAt t (hXd (C,θ) t ht)
  simpa only [Function.comp_def,← flowRhs_equivariant ε M u s hM C θ t (X (C,θ) t)] using hh

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set ODEProof MeasureTheory
variable {N : ℕ}

lemma symCongr_outer (C : Matrix (Fin N) (Fin N) ℝ) (a : Fin N → ℝ) :
    symCongr C (symOuter a) = symOuter (C *ᵥ a) := by
  apply Subtype.ext
  simp only [symCongr_apply,symOuter,mul_vecMulVec,vecMulVec_mul,vecMul_transpose]

lemma integral_outer_identity {l r : ℝ} (hlr : l ≤ r)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0) :
    (∫ t in l..r, symOuter (u t)) = symDiag (fun _ ↦ 1) := by
  have hc : ContinuousOn (fun t ↦ symOuter (u t)) (Icc l r) := continuous_symOuter.comp_continuousOn hu
  apply Subtype.ext
  ext i j
  have hh := (symEntry i j).intervalIntegral_comp_comm (hc.intervalIntegrable_of_Icc (μ := volume) hlr)
  change (∫ t in l..r, u t i*u t j) = (∫ t in l..r, symOuter (u t)).val i j at hh
  rw [← hh,ho]
  exact (diagonal_apply (fun _ : Fin N ↦ (1 : ℝ)) i j).symm

lemma integral_outer_mulVec {l r : ℝ} (hlr : l ≤ r)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) :
    (∫ t in l..r, symOuter (C *ᵥ u t)).val = C * C.transpose := by
  have hc : ContinuousOn (fun t ↦ symOuter (u t)) (Icc l r) := continuous_symOuter.comp_continuousOn hu
  have hh := (symCongr C).intervalIntegral_comp_comm (hc.intervalIntegrable_of_Icc (μ := volume) hlr)
  simp only [symCongr_outer,integral_outer_identity hlr u hu ho] at hh
  rw [hh]
  simp only [symCongr_apply,symDiag,diagonal_one,mul_one]

lemma integrate_affine_ode {E : Type u156} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {l r a b : ℝ} (hlr : l ≤ r) (X V W : ℝ → E)
    (hV : ContinuousOn V (Icc l r)) (hW : ContinuousOn W (Icc l r))
    (hd : ∀ t ∈ Icc l r, HasDerivWithinAt X (a • V t - b • W t) (Icc l r) t) :
    a • (∫ t in l..r, V t) - b • (∫ t in l..r, W t) = X r - X l := by
  have hc := (hV.const_smul a).sub (hW.const_smul b)
  have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hlr
    (HasDerivWithinAt.continuousOn hd)
    (fun t ht ↦ (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (hc.intervalIntegrable_of_Icc (μ := volume) hlr)
  have hiV : IntervalIntegrable (fun t ↦ a • V t) volume l r := by
    exact (hV.intervalIntegrable_of_Icc (μ := volume) hlr).smul a
  have hiW : IntervalIntegrable (fun t ↦ b • W t) volume l r := by
    exact (hW.intervalIntegrable_of_Icc (μ := volume) hlr).smul b
  rw [intervalIntegral.integral_sub hiV hiW,intervalIntegral.integral_smul,
    intervalIntegral.integral_smul] at hh
  exact hh

lemma flow_integral_sub {l r ε θ : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (hM : Continuous M)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (C : Matrix (Fin N) (Fin N) ℝ) (X : ℝ → Sym N)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,θ) t (X t)) (Icc l r) t) :
    (ε⁻¹ * θ) • (∫ t in l..r, M (X t)) - ε⁻¹ • (∫ t in l..r, symOuter (C *ᵥ u t)) = X r - X l := by
  apply integrate_affine_ode hlr X (fun t ↦ M (X t)) (fun t ↦ symOuter (C *ᵥ u t))
    (hM.comp_continuousOn (HasDerivWithinAt.continuousOn hXd)) _ hXd
  apply continuous_symOuter.comp_continuousOn
  exact (show Continuous (fun v : Fin N → ℝ ↦ C *ᵥ v) by fun_prop).comp_continuousOn hu

lemma flow_integral_identity {l r ε : ℝ} (hlr : l ≤ r) (hε : ε ≠ 0)
    (M : Sym N → Sym N) (hM : Continuous M) (k : Fin N → ℝ)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (X : ℝ → Sym N)
    (hXi : X l = symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,θ) t (X t)) (Icc l r) t) :
    C * C.transpose = ε • (diagonal k - (X r).val) + θ • (∫ t in l..r, M (X t)).val := by
  have hh := flow_integral_sub hlr M hM u hu C X hXd
  have he := congrArg (fun Z : Sym N ↦ ε • Z) hh
  simp only [smul_sub,smul_smul,mul_inv_cancel₀ hε,one_smul] at he
  have hcoef : ε * (ε⁻¹ * θ) = θ := by field_simp
  rw [hcoef,hXi] at he
  have he' := congrArg (fun Z : Sym N ↦ Z.val) he
  change θ • (∫ t in l..r, M (X t)).val - (∫ t in l..r, symOuter (C *ᵥ u t)).val =
    ε • (X r).val - ε • diagonal k at he'
  rw [integral_outer_mulVec hlr u hu ho C,sub_eq_iff_eq_add] at he'
  rw [he',smul_sub]
  abel

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set MeasureTheory
variable {N : ℕ}

lemma gram_entry_bound (C : Matrix (Fin N) (Fin N) ℝ) {D : ℝ}
    (hD : ‖C * C.transpose‖ ≤ D) (i j : Fin N) : |C i j| ≤ max D 0 + 1 := by
  have hsq : (C i j)^2 ≤ (C*C.transpose) i i := by
    simpa only [mul_apply,transpose_apply,pow_two] using
      (Finset.single_le_sum (fun a (_ : a ∈ (Finset.univ : Finset (Fin N))) ↦ mul_self_nonneg (C i a))
        (Finset.mem_univ j))
  have hh := hsq.trans ((le_abs_self _).trans ((matrix_norm_entry _ i i).trans hD))
  have hm := le_max_left D 0
  have hn := le_max_right D 0
  have hs := sq_abs (C i j)
  nlinarith [abs_nonneg (C i j)]

lemma bounded_integral_norm {E : Type u157} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {l r B : ℝ} (hlr : l ≤ r) (f : ℝ → E) (hf : ∀ t ∈ Icc l r, ‖f t‖ ≤ B) :
    ‖∫ t in l..r, f t‖ ≤ (r-l)*B := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const
    (fun t (ht : t ∈ Set.uIoc l r) ↦ hf t (by
      rw [uIoc_of_le hlr] at ht
      exact Ioc_subset_Icc_self ht))
  simpa only [abs_of_nonneg (sub_nonneg.mpr hlr),mul_comm] using hh

lemma matching_gram_norm {l r ε : ℝ} (hlr : l ≤ r) (hε : ε ≠ 0)
    (M : Sym N → Sym N) (hM : Continuous M) (B : ℝ≥0) (hB : ∀ A, ‖M A‖ ≤ B)
    (k : Fin N → ℝ) (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) {θ : ℝ} (hθ : θ ∈ Icc (0 : ℝ) 1) (X : ℝ → Sym N)
    (hXi : X l = symDiag k) (hXf : X r = -symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,θ) t (X t)) (Icc l r) t) :
    ‖C * C.transpose‖ ≤ |ε| *(2*‖k‖) + (r-l)*B := by
  rw [flow_integral_identity hlr hε M hM k u hu ho C θ X hXi hXd,hXf]
  have hi := bounded_integral_norm hlr (fun t ↦ M (X t)) (fun _ _ ↦ hB _)
  have he : (-(symDiag k)).val = -diagonal k := rfl
  rw [he,sub_neg_eq_add]
  apply (norm_add_le _ _).trans
  rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hθ.1]
  apply add_le_add
  · have hh := norm_add_le (diagonal k) (diagonal k)
    rw [Matrix.l2_opNorm_diagonal] at hh
    exact mul_le_mul_of_nonneg_left (hh.trans_eq (by ring)) (abs_nonneg ε)
  · exact (mul_le_of_le_one_left (norm_nonneg _) hθ.2).trans hi

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQW_LiebThirring.FlowContinuation
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Finset
noncomputable section
open Set Metric MeasureTheory Filter
open scoped Topology NNReal
noncomputable section
open Matrix Set MeasureTheory WithLp
open scoped Matrix.Norms.L2Operator Topology

namespace SharpLiebThirring.ODEProof
open Set Metric Filter

lemma scalar_stationary_unique {l r k : ℝ} (hlr : l ≤ r)
    {b q g : ℝ → ℝ} (hg : LocallyLipschitz g) (hgk : g k = 0)
    (A : ℝ≥0) (hq : ∀ t ∈ Icc l r, |q t| ≤ A)
    (hb : ∀ t ∈ Icc l r, HasDerivWithinAt b (q t * g (b t)) (Icc l r) t)
    (hbl : b l = k) : EqOn b (fun _ ↦ k) (Icc l r) := by
  have hc := HasDerivWithinAt.continuousOn hb
  obtain ⟨L,hL⟩ := hg.locallyLipschitzOn.exists_lipschitzOnWith_of_compact
    (isCompact_Icc.image_of_continuousOn hc)
  have hk : k ∈ b '' Icc l r := hbl ▸ mem_image_of_mem b ⟨le_refl _,hlr⟩
  apply ODE_solution_unique_of_mem_Icc_right (K := A*L)
    (v := fun t x ↦ q t * g x) (s := fun _ ↦ b '' Icc l r) _ hc
    (fun t ht ↦ derivative_right_of_Icc ht (hb t (Ico_subset_Icc_self ht)))
    (fun t ht ↦ mem_image_of_mem b (Ico_subset_Icc_self ht)) continuousOn_const
    (fun t _ ↦ by simpa only [hgk,mul_zero] using hasDerivWithinAt_const t (Ici t) k)
    (fun _ _ ↦ hk) hbl
  intro t ht
  apply lipschitzOnWith_iff_norm_sub_le.mpr
  intro x hx y hy
  rw [← mul_sub,norm_mul]
  calc
    _ ≤ (A : ℝ) * ((L : ℝ)*‖x-y‖) :=
      mul_le_mul (hq t (Ico_subset_Icc_self ht))
        (lipschitzOnWith_iff_norm_sub_le.mp hL hx hy) (norm_nonneg _) A.prop
    _ = _ := by push_cast; ring

end SharpLiebThirring.ODEProof
namespace SharpLiebThirring.MatrixFlow
open ODEProof Set Matrix
variable {N : ℕ}

lemma vanishing_row_stationary {l r ε : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (L Q : ℝ≥0) (hL : LipschitzWith L M)
    (q : Sym N → ℝ) (hq : ∀ A, |q A| ≤ Q)
    (g : Fin N → ℝ → ℝ) (hg : ∀ i, LocallyLipschitz (g i))
    (k : Fin N → ℝ) (hgk : ∀ i, g i (k i) = 0)
    (hc : ∀ i A, (∀ j, i ≠ j → A.val i j = 0) → (M A).val i i = q A * g i (A.val i i))
    (he : ∀ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ A, M (symConj s A) = symConj s (M A))
    (u : ℝ → Fin N → ℝ) (X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N)
    (hXi : ∀ p, X p l = symDiag k)
    (hXd : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (i : Fin N) (hi : ∀ j, C i j = 0) :
    ∀ t ∈ Icc l r, (X (C,θ) t).val i i = k i := by
  let s : Fin N → ℝ := fun j ↦ if j=i then -1 else 1
  have hs := zero_row_sign i
  have hC : (fun j a ↦ s j * C j a) = C := by
    ext j a
    by_cases hj : j=i
    · subst j; simp only [s,ite_true,hi,mul_zero]
    · simp only [s,ite_eq_right hj,one_mul]
  have hfixed : ∀ t ∈ Icc l r, symConj s (X (C,θ) t) = X (C,θ) t := by
    have hh := matrix_flow_equivariant hL k u X hXi hXd s hs (he s hs) C θ
    rw [hC] at hh
    exact fun t ht ↦ (hh ht).symm
  have hoff : ∀ t ∈ Icc l r, ∀ j, i ≠ j → (X (C,θ) t).val i j = 0 :=
    fun t ht ↦ fixed_reflection_offdiag i _ (hfixed t ht)
  have hCu (t : ℝ) : (C *ᵥ u t) i = 0 := by simp [mulVec,dotProduct,hi]
  have hd : ∀ t ∈ Icc l r, HasDerivWithinAt (fun x ↦ (X (C,θ) x).val i i)
      ((ε⁻¹*θ*q (X (C,θ) t))*g i ((X (C,θ) t).val i i)) (Icc l r) t := by
    intro t ht
    have hh := (symEntry i i).hasFDerivAt.comp_hasDerivWithinAt t (hXd (C,θ) t ht)
    change HasDerivWithinAt (fun x ↦ (X (C,θ) x).val i i)
      ((ε⁻¹*θ)*(M (X (C,θ) t)).val i i - ε⁻¹*((C*ᵥu t) i*(C*ᵥu t) i)) (Icc l r) t at hh
    simp only [hCu,mul_zero,sub_zero,hc i _ (hoff t ht)] at hh
    convert hh using 1
    ring
  have hinit : (X (C,θ) l).val i i = k i := by rw [hXi]; exact diagonal_apply_eq _ _
  let A : ℝ≥0 := ⟨|ε⁻¹*θ| * Q,mul_nonneg (abs_nonneg _) Q.prop⟩
  apply scalar_stationary_unique hlr (hg i) (hgk i) A _ hd hinit
  intro t _
  exact (abs_mul _ _).le.trans (mul_le_mul_of_nonneg_left (hq _) (abs_nonneg _))

lemma matching_nonzero_rows {l r ε : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (L Q : ℝ≥0) (hL : LipschitzWith L M)
    (q : Sym N → ℝ) (hq : ∀ A, |q A| ≤ Q)
    (g : Fin N → ℝ → ℝ) (hg : ∀ i, LocallyLipschitz (g i))
    (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) (hgk : ∀ i, g i (k i) = 0)
    (hc : ∀ i A, (∀ j, i ≠ j → A.val i j = 0) → (M A).val i i = q A * g i (A.val i i))
    (he : ∀ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ A, M (symConj s A) = symConj s (M A))
    (u : ℝ → Fin N → ℝ) (X : (Matrix (Fin N) (Fin N) ℝ × ℝ) → ℝ → Sym N)
    (hXi : ∀ p, X p l = symDiag k)
    (hXd : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (X p) (flowRhs ε M u p t (X p t)) (Icc l r) t)
    (C : Matrix (Fin N) (Fin N) ℝ) (θ : ℝ) (hXf : X (C,θ) r = -symDiag k) :
    ∀ i, ∃ j, C i j ≠ 0 := by
  intro i
  by_contra hn
  push Not at hn
  have hh := vanishing_row_stationary hlr M L Q hL q hq g hg k hgk hc he u X hXi hXd C θ i hn r ⟨hlr,le_refl _⟩
  rw [hXf] at hh
  change -diagonal k i i = k i at hh
  rw [diagonal_apply_eq] at hh
  linarith [hk i]

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open Matrix Set ContinuationGap
variable {N : ℕ}

lemma isClosed_lower : IsClosed {C : Matrix (Fin N) (Fin N) ℝ | ∀ i j, i < j → C i j = 0} := by
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  apply isClosed_iInter
  intro j
  apply isClosed_iInter
  intro _
  exact isClosed_eq (by fun_prop) continuous_const

lemma compact_lower_box (R : ℝ) : IsCompact {C : LowerSpace N | ∀ i j, |C.val i j| ≤ R} := by
  have hh := (isClosed_lower (N := N)).isClosedEmbedding_subtypeVal.isCompact_preimage
    (isCompact_Icc : IsCompact (Icc (fun _ _ : Fin N ↦ -R) (fun _ _ : Fin N ↦ R)))
  convert! hh using 1
  ext C
  change (∀ i j, |C.val i j| ≤ R) ↔ ((∀ i j, -R ≤ C.val i j) ∧ (∀ i j, C.val i j ≤ R))
  constructor
  · intro h
    exact ⟨fun i j ↦ (abs_le.mp (h i j)).1,fun i j ↦ (abs_le.mp (h i j)).2⟩
  · rintro ⟨hl,hu⟩ i j
    exact abs_le.mpr ⟨hl i j,hu i j⟩

lemma compact_matching_zeros (Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ)
    (hc : Continuous (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1))
    (R : ℝ) (hb : ∀ θ ∈ Icc (0 : ℝ) 1, ∀ C, Φ θ C = 0 → ∀ i j, |C.val i j| ≤ R) :
    IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0} := by
  apply ((compact_lower_box R).prod isCompact_Icc).of_isClosed_subset
    ((isClosed_Icc.preimage continuous_snd).inter (isClosed_eq hc continuous_const))
  intro z hz
  exact ⟨hb z.2 hz.1 z.1 hz.2,hz.1⟩

end SharpLiebThirring.MatrixFlow
namespace SharpLiebThirring.MatrixFlow
open ODEProof Set Matrix ContinuationGap
variable {N : ℕ}

lemma terminal_zero_parameter {l r ε : ℝ} (hlr : l ≤ r)
    (M : Sym N → Sym N) (hM : Continuous M) (k : Fin N → ℝ)
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0)
    (C : Matrix (Fin N) (Fin N) ℝ) (X : ℝ → Sym N)
    (hXi : X l = symDiag k)
    (hXd : ∀ t ∈ Icc l r, HasDerivWithinAt X (flowRhs ε M u (C,0) t (X t)) (Icc l r) t) :
    (X r + symDiag k).val = 2 • diagonal k - ε⁻¹ • (C*C.transpose) := by
  have hh := flow_integral_sub hlr M hM u hu C X hXd
  simp only [mul_zero,zero_smul,zero_sub,hXi] at hh
  have he := congrArg (fun A : Sym N ↦ A.val) hh
  change -(ε⁻¹ • (∫ t in l..r, symOuter (C*ᵥu t)).val) = (X r).val - diagonal k at he
  rw [integral_outer_mulVec hlr u hu ho C] at he
  have he' := sub_eq_iff_eq_add.mp he.symm
  change (X r).val + diagonal k = _
  rw [he']
  simp only [two_smul]
  abel

lemma terminal_matching_oai {l r ε : ℝ} (hlr : l ≤ r) (hε : 0 < ε)
    (M : Sym N → Sym N) (L B Q : ℝ≥0) (hL : LipschitzWith L M) (hB : ∀ A, ‖M A‖ ≤ B)
    (q : Sym N → ℝ) (hq : ∀ A, |q A| ≤ Q)
    (g : Fin N → ℝ → ℝ) (hg : ∀ i, LocallyLipschitz (g i))
    (k : Fin N → ℝ) (hk : ∀ i, 0 < k i) (hgk : ∀ i, g i (k i) = 0)
    (hc : ∀ i A, (∀ j, i ≠ j → A.val i j = 0) → (M A).val i i = q A * g i (A.val i i))
    (he : ∀ s : Fin N → ℝ, (∀ i, s i = 1 ∨ s i = -1) → ∀ A, M (symConj s A) = symConj s (M A))
    (u : ℝ → Fin N → ℝ) (hu : ContinuousOn u (Icc l r))
    (ho : ∀ i j, (∫ t in l..r, u t i * u t j) = if i=j then 1 else 0) :
    ∃ (C : LowerSpace N) (X : ℝ → Sym N), X l = symDiag k ∧ X r = -symDiag k ∧
      (∀ t ∈ Icc l r, HasDerivWithinAt X (ε⁻¹ • (M (X t) - symOuter (C.val *ᵥ u t))) (Icc l r) t) ∧
      ‖C.val * C.val.transpose‖ ≤ |ε| * (2*‖k‖) + (r-l)*B := by
  obtain ⟨Y,hYi,hYd,hYc⟩ := matrix_flow_exists hlr ε k u hu M L B hL hB
  let Φ : ℝ → LowerSpace N → Matrix (Fin N) (Fin N) ℝ := fun θ C ↦ (Y (C.val,θ) r + symDiag k).val
  have hΦc : Continuous (fun z : LowerSpace N × ℝ ↦ Φ z.2 z.1) := by
    have hYr : Continuous (fun p ↦ Y p r) := hYc.comp
      (continuous_id.prodMk (continuous_const (y := (⟨r,hlr,le_refl r⟩ : Icc l r))))
    exact ((hYr.comp ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).add continuous_const).subtype_val
  have hzero (θ : ℝ) (C : LowerSpace N) (h : Φ θ C = 0) : Y (C.val,θ) r = -symDiag k := by
    apply eq_neg_iff_add_eq_zero.mpr
    apply Subtype.ext
    exact h
  have hsym (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) 1) (C : LowerSpace N) : (Φ θ C).IsHermitian :=
    (Y (C.val,θ) r + symDiag k).prop
  have heq (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) 1) (C : LowerSpace N)
      (s : Fin N → ℝ) (hs : ∀ i, s i = 1 ∨ s i = -1) :
      Φ θ (rowSign s C) = signConjugate s (Φ θ C) := by
    have hh := matrix_flow_equivariant hL k u Y hYi hYd s hs (he s hs) C.val θ ⟨hlr,le_refl r⟩
    change (Y ((rowSign s C).val,θ) r + symDiag k).val = (symConj s (Y (C.val,θ) r + symDiag k)).val
    rw [map_add,symConj_diag s hs]
    exact congrArg (fun A : Sym N ↦ (A + symDiag k).val) hh
  have hinit (C : LowerSpace N) : Φ 0 C = 2 • diagonal k - ε⁻¹ • (C.val*C.val.transpose) :=
    terminal_zero_parameter hlr M hL.continuous k u hu ho C.val (Y (C.val,0)) (hYi _) (hYd _)
  have hcomp : IsCompact {z : LowerSpace N × ℝ | z.2 ∈ Icc (0 : ℝ) 1 ∧ Φ z.2 z.1 = 0} := by
    apply compact_matching_zeros Φ hΦc (max (|ε| * (2*‖k‖) + (r-l)*B) 0 + 1)
    intro θ hθ C hC
    exact gram_entry_bound C.val (matching_gram_norm hlr (ne_of_gt hε) M hL.continuous B hB k u hu ho C.val
      hθ (Y (C.val,θ)) (hYi _) (hzero θ C hC) (hYd _))
  have hn (θ : ℝ) (_ : θ ∈ Icc (0 : ℝ) 1) (C : LowerSpace N) (hC : Φ θ C = 0) : NonzeroRows C :=
    matching_nonzero_rows hlr M L Q hL q hq g hg k hk hgk hc he u Y hYi hYd C.val θ (hzero θ C hC)
  obtain ⟨C,hC⟩ := PathTopology.equivariant_continuation N ε k hε hk Φ hΦc.continuousOn hsym heq hinit hcomp hn
  refine ⟨C,Y (C.val,1),hYi _,hzero 1 C hC,?_,?_⟩
  · intro t ht
    simpa only [flowRhs,mul_one,smul_sub] using hYd (C.val,1) t ht
  · exact matching_gram_norm hlr (ne_of_gt hε) M hL.continuous B hB k u hu ho C.val
      ⟨zero_le_one,le_refl _⟩ (Y (C.val,1)) (hYi _) (hzero 1 C hC) (hYd _)

end SharpLiebThirring.MatrixFlow

end
end
end
end
end

end OAI
end

theorem solution : type_of% @OAI.SharpLiebThirring.MatrixFlow.terminal_matching_oai := @OAI.SharpLiebThirring.MatrixFlow.terminal_matching_oai
