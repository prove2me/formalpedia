-- Prove2me | solution 1 for LatticePrepro.lattice_gap
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T15:54:46.012117+00:00
-- url     : https://prove2.me/submissions/2df5269f-a27d-47cb-a42d-d746af5e04cd

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Reduction_LinearSystem
import Definitions.Def_LatticePrepro_Conversions_Codes
import Definitions.Def_LatticePrepro_Conversions_ConstructionA
import Definitions.Def_LatticePrepro_Conversions_Hadamard
import Definitions.Def_LatticePrepro_Conversions_Lattices
import Definitions.Def_LatticePrepro_Lattices_Distance
import Definitions.Def_LatticePrepro_Lattices_Mathlib
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Verifier_Quadratic
import Definitions.Def_LatticePrepro_Reduction_FixedSystem
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Hankel
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_ElementTable
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Definitions.Def_LatticePrepro_Tables_Explicit
import Definitions.Def_LatticePrepro_Main
import Theorems.Thm_LatticePrepro_exists_gapReduction
import Theorems.Thm_LatticePrepro_exists_latticeReduction
import Theorems.Thm_LatticePrepro_params_spec

namespace LatticePrepro end LatticePrepro

namespace LatticePrepro

namespace LinearSystemFamily

variable {F : Type} [Field F] {X : Type}

variable (L : LinearSystemFamily F X)

/-- Number of columns `n = D · b`. -/
lemma card_ι : Fintype.card L.ι = L.numBlocks * L.blockSize := by
  classical
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := L.blk) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  simp [L.card_fiber, Finset.sum_const, numBlocks]

end LinearSystemFamily

end LatticePrepro

namespace LatticePrepro

namespace PNorm

lemma one_le_s (pn : PNorm) : 1 ≤ pn.s := by
  cases pn with
  | fin p hp => exact le_min hp (by norm_num)
  | inf => norm_num [PNorm.s]

lemma s_le_two (pn : PNorm) : pn.s ≤ 2 := by
  cases pn with
  | fin p hp => exact min_le_right _ _
  | inf => norm_num [PNorm.s]

lemma norm_nonneg {M : Type} [Fintype M] (pn : PNorm) (v : M → ℝ) : 0 ≤ pn.norm v := by
  cases pn with
  | fin p hp =>
      show 0 ≤ (∑ i, |v i| ^ p) ^ (1 / p)
      exact Real.rpow_nonneg (Finset.sum_nonneg fun i _ => Real.rpow_nonneg (abs_nonneg _) _) _
  | inf =>
      show 0 ≤ ⨆ i, |v i|
      exact Real.iSup_nonneg fun i => abs_nonneg _

end PNorm

end LatticePrepro

namespace LatticePrepro

namespace PNorm

variable {M : Type} [Fintype M]

/-- Every coordinate is bounded in absolute value by the `ℓ_p` norm. -/
lemma abs_apply_le_norm (pn : PNorm) (w : M → ℝ) (i : M) : |w i| ≤ pn.norm w := by
  cases pn with
  | fin p hp =>
    show |w i| ≤ (∑ j, |w j| ^ p) ^ (1 / p)
    have hp0 : 0 < p := by linarith
    have h1 : |w i| ^ p ≤ ∑ j, |w j| ^ p :=
      Finset.single_le_sum (f := fun j => |w j| ^ p)
        (fun j _ => Real.rpow_nonneg (abs_nonneg _) _) (Finset.mem_univ i)
    calc |w i| = (|w i| ^ p) ^ (1 / p) := by
          rw [← Real.rpow_mul (abs_nonneg _), mul_one_div_cancel hp0.ne', Real.rpow_one]
      _ ≤ (∑ j, |w j| ^ p) ^ (1 / p) :=
          Real.rpow_le_rpow (Real.rpow_nonneg (abs_nonneg _) _) h1 (by positivity)
  | inf =>
    show |w i| ≤ ⨆ j, |w j|
    exact le_ciSup (Set.finite_range fun j => |w j|).bddAbove i

end PNorm

namespace LatticeFamily

variable {X : Type} (Λ : LatticeFamily X) (pn : PNorm) (x : X)

lemma dist_nonneg (v : Λ.M → ℤ) : 0 ≤ Λ.dist pn x v := pn.norm_nonneg _

lemma bddBelow_range_dist : BddBelow (Set.range fun v : Λ.lattice => Λ.dist pn x v) :=
  ⟨0, by rintro _ ⟨v, rfl⟩; exact Λ.dist_nonneg pn x v⟩

theorem latticeDist_le {v : Λ.M → ℤ} (hv : v ∈ Λ.lattice) :
    Λ.latticeDist pn x ≤ Λ.dist pn x v :=
  ciInf_le (Λ.bddBelow_range_dist pn x) ⟨v, hv⟩

theorem le_latticeDist {d : ℝ} (h : ∀ v ∈ Λ.lattice, d ≤ Λ.dist pn x v) :
    d ≤ Λ.latticeDist pn x :=
  le_ciInf fun v => h v v.2

theorem latticeDist_le_of_exists {R : ℝ} (h : ∃ v ∈ Λ.lattice, Λ.dist pn x v ≤ R) :
    Λ.latticeDist pn x ≤ R := by
  obtain ⟨v, hv, hvR⟩ := h
  exact (Λ.latticeDist_le pn x hv).trans hvR

/-- The lattice vectors within distance `K` of the target form a finite set: every coordinate of
`t_x - v` is bounded by `K`. -/
lemma finite_dist_le (K : ℝ) : {v : Λ.M → ℤ | v ∈ Λ.lattice ∧ Λ.dist pn x v ≤ K}.Finite := by
  refine Set.Finite.subset (Set.Finite.pi' (κ := fun _ : Λ.M => ℤ)
    (t := fun i => Set.Icc (Λ.target x i - ⌈K⌉) (Λ.target x i + ⌈K⌉))
    fun _ => Set.finite_Icc _ _) ?_
  intro v hv i
  have h1 := pn.abs_apply_le_norm (toReal (Λ.target x - v)) i
  have h2 : ((|Λ.target x i - v i| : ℤ) : ℝ) ≤ K := by
    rw [Int.cast_abs]
    exact h1.trans hv.2
  have h3 : |Λ.target x i - v i| ≤ ⌈K⌉ := Int.cast_le.mp (h2.trans (Int.le_ceil K))
  rw [abs_le] at h3
  simp only [Set.mem_Icc]
  omega

/-- **The infimum is attained**: some lattice vector realizes `dist_p(t_x, Λ)`. -/
theorem exists_dist_eq_latticeDist : ∃ v ∈ Λ.lattice, Λ.dist pn x v = Λ.latticeDist pn x := by
  set T : Set (Λ.M → ℤ) := {v | v ∈ Λ.lattice ∧ Λ.dist pn x v ≤ Λ.dist pn x 0} with hT
  have hT0 : (0 : Λ.M → ℤ) ∈ T := ⟨Λ.lattice.zero_mem, le_rfl⟩
  obtain ⟨v, ⟨hvL, -⟩, hmin⟩ :=
    Set.exists_min_image T (Λ.dist pn x) (Λ.finite_dist_le pn x _) ⟨0, hT0⟩
  refine ⟨v, hvL, le_antisymm ?_ (Λ.latticeDist_le pn x hvL)⟩
  refine Λ.le_latticeDist pn x fun w hw => ?_
  by_cases hwK : Λ.dist pn x w ≤ Λ.dist pn x 0
  · exact hmin w ⟨hw, hwK⟩
  · exact (hmin 0 hT0).trans (not_le.mp hwK).le

theorem lt_latticeDist_of_forall {d : ℝ} (h : ∀ v ∈ Λ.lattice, d < Λ.dist pn x v) :
    d < Λ.latticeDist pn x := by
  obtain ⟨v, hv, hd⟩ := Λ.exists_dist_eq_latticeDist pn x
  rw [← hd]
  exact h v hv

end LatticeFamily

end LatticePrepro

namespace LatticePrepro

lemma momentAxes_spec {δ : ℝ} (hδ1 : δ < 1) :
    1 ≤ momentAxes δ ∧ δ * (momentAxes δ + 1) < momentAxes δ := by
  refine ⟨by unfold momentAxes; omega, ?_⟩
  have h1δ : 0 < 1 - δ := by linarith
  have hm : δ / (1 - δ) < momentAxes δ := by
    unfold momentAxes
    push_cast
    linarith [Nat.le_ceil (δ / (1 - δ))]
  rw [div_lt_iff₀ h1δ] at hm
  nlinarith

/-- From the parameter choice: `16 · M^δ ≤ g` whenever `M ≤ 4 n` and `64 n^δ ≤ g`. -/
lemma rpow_le_of_le_four_mul {M n : ℕ} {g δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hM : M ≤ 4 * n)
    (h64 : 64 * (n : ℝ) ^ δ ≤ g) : 16 * (M : ℝ) ^ δ ≤ g := by
  have hMR : (M : ℝ) ≤ 4 * n := by exact_mod_cast hM
  calc 16 * (M : ℝ) ^ δ ≤ 16 * (4 * (n : ℝ)) ^ δ := by gcongr
    _ = 16 * (4 : ℝ) ^ δ * (n : ℝ) ^ δ := by rw [Real.mul_rpow (by norm_num) (by positivity)]; ring
    _ ≤ 16 * 4 * (n : ℝ) ^ δ := by
        gcongr
        calc (4 : ℝ) ^ δ ≤ (4 : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hδ1
          _ = 4 := Real.rpow_one 4
    _ = 64 * (n : ℝ) ^ δ := by ring
    _ ≤ g := h64

/-- **Theorem 5.1 for lattices**, with the explicit exponent `C = sizeExp 2 (1 - s ε)`: for every
norm exponent `1 ≤ p ≤ ∞` with `s = min {p, 2}`, every `0 < ε < 1/s` and every quadratic
verifier `V` over `𝔽_2`, there is a fixed full-rank lattice `Λ ⊆ ℤ^M` with `M ≤ (S + 1)^C` and
gap `M^{1/s - ε}` for `L(V)`. -/
private theorem lattice_gap (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    (V : QuadraticVerifier 2) :
    Nonempty (LatticeGap pn ε V.Language (V.S + 1) (sizeExp 2 (1 - pn.s * ε))) := by
  have hs1 := pn.one_le_s
  have hs2 := pn.s_le_two
  have hs0 : 0 < pn.s := by linarith
  set δ : ℝ := 1 - pn.s * ε with hδ
  have hδ0 : 0 ≤ δ := by
    rw [hδ]
    have := (lt_div_iff₀ hs0).mp hε1
    linarith
  have hδ1 : δ < 1 := by rw [hδ]; nlinarith
  have hm := (momentAxes_spec hδ1).1
  have hS1 : 1 ≤ V.S := by have := V.n_succ_le; omega
  obtain ⟨⟨L, hL, hgb, -, hDpos, hsize⟩⟩ := exists_gapReduction 2 V ((V.S + 1) ^ gapExp 2 δ)
    (momentAxes δ) (Nat.one_le_pow _ _ (by omega)) hm
  set n := Fintype.card L.ι with hn
  have hn1 : 1 ≤ n := by
    rw [hn, L.card_ι]
    exact Nat.mul_pos hDpos (by omega)
  obtain ⟨h64, hC⟩ := params_spec 2 hδ0 hδ1 V.S n hS1 hn1 hsize
  set g := (V.S + 1) ^ gapExp 2 δ with hg
  obtain ⟨Red⟩ := exists_latticeReduction L hgb hDpos pn
  set Λ := Red.Λ with hΛ
  have hM4 : Fintype.card Λ.M ≤ 4 * n := Red.card_lt_four_mul.le
  have h2n : 2 * n ≤ Fintype.card Λ.M := Red.two_mul_card_le
  have hMδ : 16 * (Fintype.card Λ.M : ℝ) ^ δ ≤ g := rpow_le_of_le_four_mul hδ0 hδ1.le hM4 h64
  have hexp : δ * (pn.s)⁻¹ = 1 / pn.s - ε := by rw [hδ]; field_simp
  have hRR : (0 : ℝ) < Red.R := by exact_mod_cast Red.one_le_R
  have hDR : (0 : ℝ) < L.numBlocks := by exact_mod_cast hDpos
  -- NO instances: every lattice vector is far from the target
  have hno : ∀ x ∉ V.Language, ∀ v ∈ Λ.lattice,
      (Fintype.card Λ.M : ℝ) ^ (1 / pn.s - ε) * Red.R < Λ.dist pn x v := by
    intro x hx v hv
    have hgw : (g : ℝ) * L.numBlocks < Red.weight x v := by
      exact_mod_cast Red.lt_weight x (hL.2 x hx) v hv
    have hdist0 : 0 ≤ Λ.dist pn x v := pn.norm_nonneg _
    -- `g D < w ≤ 16 D (dist/R)^s`, hence `g / 16 < (dist/R)^s`
    have h1 : (g : ℝ) < 16 * (Λ.dist pn x v / Red.R) ^ pn.s := by
      have : (g : ℝ) * L.numBlocks < 16 * (Λ.dist pn x v / Red.R) ^ pn.s * L.numBlocks := by
        calc (g : ℝ) * L.numBlocks < Red.weight x v := hgw
          _ ≤ 16 * L.numBlocks * (Λ.dist pn x v / Red.R) ^ pn.s := Red.weight_le x v hv
          _ = 16 * (Λ.dist pn x v / Red.R) ^ pn.s * L.numBlocks := by ring
      exact lt_of_mul_lt_mul_right this hDR.le
    have h2 : (Fintype.card Λ.M : ℝ) ^ δ < (Λ.dist pn x v / Red.R) ^ pn.s := by linarith
    -- take `(1/s)`-th powers
    have h3 : ((Fintype.card Λ.M : ℝ) ^ δ) ^ (pn.s)⁻¹ <
        ((Λ.dist pn x v / Red.R) ^ pn.s) ^ (pn.s)⁻¹ :=
      Real.rpow_lt_rpow (by positivity) h2 (by positivity)
    rw [Real.rpow_rpow_inv (by positivity) hs0.ne', ← Real.rpow_mul (by positivity)] at h3
    rw [hexp, lt_div_iff₀ hRR] at h3
    exact h3
  refine ⟨⟨Λ, Red.R, Red.one_le_R, by omega, by omega, Red.N, Red.N_pos, Red.smul_mem,
    fun x hx => Λ.latticeDist_le_of_exists pn x (Red.yes x (hL.1 x hx)),
    fun x hx => Λ.lt_latticeDist_of_forall pn x (hno x hx)⟩⟩

end LatticePrepro

open LatticePrepro
theorem solution (pn : PNorm) (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / pn.s)
    (V : QuadraticVerifier 2) :
    Nonempty (LatticeGap pn ε V.Language (V.S + 1) (sizeExp 2 (1 - pn.s * ε))) :=
  @LatticePrepro.lattice_gap pn ε hε hε1 V
