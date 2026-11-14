-- Prove2me | solution 1 for LatticePrepro.ExplicitTables.soundness_setup
-- status  : ACCEPTED   (prove)
-- author  : @WizardOfMenlo
-- created : 2026-11-13T09:33:04.055782+00:00
-- url     : https://prove2.me/submissions/fa5d88a9-2e07-41e9-a74b-bd800ea6719f

import Mathlib
import Definitions.Def_LatticePrepro_Basic_Blocks
import Definitions.Def_LatticePrepro_Moments_Basic
import Definitions.Def_LatticePrepro_Moments_Representation
import Definitions.Def_LatticePrepro_Tables_Digits
import Definitions.Def_LatticePrepro_Tables_FieldSetup
import Definitions.Def_LatticePrepro_Tables_Construction
import Definitions.Def_LatticePrepro_Tables_TableSoundness
import Theorems.Thm_LatticePrepro_card_mul_rank_eval_le
import Theorems.Thm_LatticePrepro_digitVal_gdigits
import Theorems.Thm_LatticePrepro_exists_dependence_of_rank_le
import Theorems.Thm_LatticePrepro_gdigits_le

namespace LatticePrepro end LatticePrepro
namespace LatticePrepro.ExplicitTables end LatticePrepro.ExplicitTables

namespace LatticePrepro

lemma digitVal_add (B : ℕ) {m : ℕ} (η η' : Fin m → ℕ) :
    digitVal B (η + η') = digitVal B η + digitVal B η' := by
  simp [digitVal, add_mul, Finset.sum_add_distrib]

end LatticePrepro

namespace LatticePrepro

open Polynomial

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

section Interpolation

variable {FS m}

/-- The interpolant takes the prescribed values at the nodes. -/
lemma eval_interp (y : Coord FS m → ZMod p) (η : Fin m → ℕ) (s : FS.𝕊) :
    eval s (interp FS m y η) = colSum FS m y η s := by
  unfold interp
  have := Lagrange.eval_interpolate_at_node (r := fun s => colSum FS m y η s)
    (Set.injOn_id _) (Finset.mem_univ s)
  simpa using this

lemma degree_interp_lt (y : Coord FS m → ZMod p) (η : Fin m → ℕ) :
    (interp FS m y η).degree < Fintype.card FS.𝕊 := by
  unfold interp
  have := Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset FS.𝕊)) (v := id)
    (r := fun s => colSum FS m y η s) (Set.injOn_id _)
  simpa using this

lemma coeff_interp_eq_zero_of_card_le (y : Coord FS m → ZMod p) (η : Fin m → ℕ) {u : ℕ}
    (hu : Fintype.card FS.𝕊 ≤ u) : (interp FS m y η).coeff u = 0 :=
  coeff_eq_zero_of_degree_lt ((degree_interp_lt y η).trans_le (by exact_mod_cast hu))

end Interpolation

/-- Build an index from an exponent vector with small entries. -/
def IdxSet.ofNat {p m B : ℕ} (η : Fin m → ℕ) (hη : ∀ h, η h ≤ 2 * p * (B - 1)) : IdxSet p m B :=
  fun h => ⟨η h, Nat.lt_succ_of_le (hη h)⟩

@[simp] lemma IdxSet.toNat_ofNat {p m B : ℕ} (η : Fin m → ℕ) (hη : ∀ h, η h ≤ 2 * p * (B - 1)) :
    (IdxSet.ofNat η hη).toNat = η := by
  funext h; rfl

section Unpack

variable {FS m B}

/-- Low-degree constraint: coefficients above `Δ` vanish. -/
lemma coeff_interp_eq_zero_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (η : IdxSet p m B) {u : ℕ} (hu : degBound p m B δ < u) :
    (interp FS m y η.toNat).coeff u = 0 := by
  by_cases hq : Fintype.card FS.𝕊 ≤ u
  · exact coeff_interp_eq_zero_of_card_le y _ hq
  · have hq' := not_le.mp hq
    have := congrFun (congrArg Prod.fst hy) (η, ⟨u, hq'⟩)
    simpa [constraintFun, hu] using this

/-- The interpolants of indexed exponent vectors have degree at most `Δ`. -/
lemma natDegree_interp_le_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (η : IdxSet p m B) :
    (interp FS m y η.toNat).natDegree ≤ degBound p m B δ :=
  natDegree_le_iff_coeff_eq_zero.mpr fun _ hN => coeff_interp_eq_zero_of_constraint hy η hN

/-- Index-consistency constraint. -/
lemma aeval_interp_eq_mom_of_constraint {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (η : IdxSet p m B) :
    aeval FS.γ (interp FS m y η.toNat) = mom FS m B y (digitVal B η.toNat) := by
  have := congrFun (congrArg (fun w => w.2.1) hy) η
  simpa [constraintFun, sub_eq_zero] using this

end Unpack

end ExplicitTables

end LatticePrepro

namespace LatticePrepro

open Polynomial Matrix

namespace ExplicitTables

variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)

/-- The matrix `E` with entries `λ^{digits(h)}`. -/
noncomputable def Emat : Matrix (Fin (hLen p m B)) (Fin m → FS.𝕊) FS.𝕊 :=
  Matrix.of fun h lam => ∏ g, lam g ^ gdigits B m h.val g

/-- The polynomial matrix of a table (Definition A.5). -/
noncomputable def Hmat (y : Coord FS m → ZMod p) :
    Matrix (Fin (hLen p m B)) (Fin (hLen p m B)) FS.𝕊[X] :=
  Matrix.of fun h h' => interp FS m y (gdigits B m h.val + gdigits B m h'.val)

variable {FS m B}

lemma gdigits_hLen_le (hB : 2 ≤ B) (hm : 1 ≤ m) (h : Fin (hLen p m B)) (g : Fin m) :
    gdigits B m h.val g ≤ p * (B - 1) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have hk : h.val ≤ p * (B ^ m - 1) := by
    have := h.isLt; unfold hLen at this; omega
  exact gdigits_le hB hm hp hk g

lemma hankelExp_le (hB : 2 ≤ B) (hm : 1 ≤ m) (h h' : Fin (hLen p m B)) (g : Fin m) :
    (gdigits B m h.val + gdigits B m h'.val) g ≤ 2 * p * (B - 1) := by
  have h1 := gdigits_hLen_le hB hm h g
  have h2 := gdigits_hLen_le hB hm h' g
  simp only [Pi.add_apply]
  rw [mul_assoc]; omega

/-- The exponent vector of a Hankel entry, as an index. -/
def hankelIdx (hB : 2 ≤ B) (hm : 1 ≤ m) (h h' : Fin (hLen p m B)) : IdxSet p m B :=
  IdxSet.ofNat (gdigits B m h.val + gdigits B m h'.val) (hankelExp_le hB hm h h')

lemma hankelIdx_toNat (hB : 2 ≤ B) (hm : 1 ≤ m) (h h' : Fin (hLen p m B)) :
    (hankelIdx hB hm h h').toNat = gdigits B m h.val + gdigits B m h'.val :=
  IdxSet.toNat_ofNat _ _

/-- Entries of the polynomial matrix have degree at most `Δ`. -/
lemma natDegree_Hmat_le (hB : 2 ≤ B) (hm : 1 ≤ m) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (h h' : Fin (hLen p m B)) :
    (Hmat FS m B y h h').natDegree ≤ degBound p m B δ := by
  have := natDegree_interp_le_of_constraint hy (hankelIdx hB hm h h')
  rwa [hankelIdx_toNat] at this

/-- Evaluating the polynomial matrix at a node `s` gives `E · diag(y(·, s)) · Eᵀ`. -/
lemma Hmat_map_eval (y : Coord FS m → ZMod p) (s : FS.𝕊) :
    (Hmat FS m B y).map (eval s) =
      Emat FS m B * Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s))) *
        (Emat FS m B)ᵀ := by
  ext h h'
  simp only [Hmat, Matrix.map_apply, Matrix.of_apply, eval_interp, colSum]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Emat, Matrix.of_apply]
  refine Finset.sum_congr rfl fun lam _ => ?_
  rw [Algebra.smul_def]
  simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

/-- The rank of `Hmat y (s)` is at most the weight of column `s`. -/
lemma rank_Hmat_map_eval_le (y : Coord FS m → ZMod p) (s : FS.𝕊) :
    ((Hmat FS m B y).map (eval s)).rank ≤ (Finset.univ.filter fun lam => y (lam, s) ≠ 0).card := by
  classical
  rw [Hmat_map_eval]
  calc (Emat FS m B * Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s))) *
        (Emat FS m B)ᵀ).rank
      ≤ (Emat FS m B * Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s)))).rank :=
        Matrix.rank_mul_le_left _ _
    _ ≤ (Matrix.diagonal (fun lam => algebraMap (ZMod p) FS.𝕊 (y (lam, s)))).rank :=
        Matrix.rank_mul_le_right _ _
    _ = Fintype.card {lam // algebraMap (ZMod p) FS.𝕊 (y (lam, s)) ≠ 0} := Matrix.rank_diagonal _
    _ = (Finset.univ.filter fun lam => y (lam, s) ≠ 0).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext lam
        simp [(algebraMap (ZMod p) FS.𝕊).injective.eq_iff' (map_zero _)]

/-- The Hamming weight is the sum of the column weights. -/
lemma hammingNorm_eq_sum_cols (y : Coord FS m → ZMod p) :
    hammingNorm y = ∑ s : FS.𝕊, (Finset.univ.filter fun lam => y (lam, s) ≠ 0).card := by
  classical
  unfold hammingNorm
  rw [Finset.card_eq_sum_card_fiberwise (f := Prod.snd) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun s _ => ?_
  refine Finset.card_bij (fun c _ => c.1) ?_ ?_ ?_
  · intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    rw [← hc.2]; exact hc.1
  · intro c hc c' hc' h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc hc'
    exact Prod.ext h (hc.2.trans hc'.2.symm)
  · intro lam hlam
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hlam
    exact ⟨(lam, s), by simpa using hlam, rfl⟩

lemma sum_rank_Hmat_map_eval_le (y : Coord FS m → ZMod p) :
    ∑ s : FS.𝕊, ((Hmat FS m B y).map (eval s)).rank ≤ hammingNorm y := by
  rw [hammingNorm_eq_sum_cols]
  exact Finset.sum_le_sum fun s _ => rank_Hmat_map_eval_le y s

/-- Evaluating the polynomial matrix at `γ` gives the Hankel matrix of the moments. -/
lemma Hmat_map_aeval (hB : 2 ≤ B) (hm : 1 ≤ m) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (h h' : Fin (hLen p m B)) :
    ((Hmat FS m B y).map (aeval FS.γ)) h h' = mom FS m B y (h.val + h'.val) := by
  simp only [Hmat, Matrix.map_apply, Matrix.of_apply]
  have := aeval_interp_eq_mom_of_constraint hy (hankelIdx hB hm h h')
  rw [hankelIdx_toNat, digitVal_add, digitVal_gdigits hB hm, digitVal_gdigits hB hm] at this
  exact this

/-- The rank inequality `q ρ ≤ wt(y) + Δ ρ` for the Hankel matrix. -/
lemma card_mul_rank_hankel_le (hB : 2 ≤ B) (hm : 1 ≤ m) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) :
    Fintype.card FS.𝕊 * ((Hmat FS m B y).map (aeval FS.γ)).rank ≤
      hammingNorm y + degBound p m B δ * ((Hmat FS m B y).map (aeval FS.γ)).rank := by
  have := card_mul_rank_eval_le FS.γ (Hmat FS m B y) (natDegree_Hmat_le hB hm hy)
  exact this.trans (Nat.add_le_add_right (sum_rank_Hmat_map_eval_le y) _)

/-- **Soundness setup**: for a constrained table of weight below the threshold, the Hankel
matrix of its moments has rank `t < B^m` with `q t ≤ 2 wt(y)`, and its first `t + 1` columns
are linearly dependent. -/
private theorem soundness_setup (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (hw : 2 * hammingNorm y < B ^ m * Fintype.card FS.𝕊) :
    ∃ t : ℕ, t < B ^ m ∧ Fintype.card FS.𝕊 * t ≤ 2 * hammingNorm y ∧
      ∃ c : Fin (t + 1) → FS.K, c ≠ 0 ∧
        ∀ i : Fin (hLen p m B), ∑ j, c j * mom FS m B y (i.val + j.val) = 0 := by
  set q := Fintype.card FS.𝕊 with hq
  set Δ := degBound p m B δ with hΔdef
  set ρ := ((Hmat FS m B y).map (aeval FS.γ)).rank with hρ
  set w := hammingNorm y with hwdef
  have h1 : q * ρ ≤ w + Δ * ρ := card_mul_rank_hankel_le hB hm hy
  have h4 : 4 * (Δ * ρ) ≤ q * ρ := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right ρ hΔ.le
  have h3 : 3 * (q * ρ) ≤ 4 * w := by omega
  have hqρ : q * ρ ≤ 2 * w := by omega
  have hρr : ρ < B ^ m := by
    have h5 : (3 * ρ) * q < (2 * B ^ m) * q := by
      calc (3 * ρ) * q = 3 * (q * ρ) := by ring
        _ ≤ 4 * w := h3
        _ < 2 * (B ^ m * q) := by omega
        _ = (2 * B ^ m) * q := by ring
    have := Nat.lt_of_mul_lt_mul_right h5
    omega
  have hp : 1 ≤ p := (Fact.out : p.Prime).pos
  have hrℓ : B ^ m ≤ hLen p m B := by
    unfold hLen
    have h1 : 1 ≤ B ^ m := Nat.one_le_pow _ _ (by omega)
    have : B ^ m - 1 ≤ p * (B ^ m - 1) := Nat.le_mul_of_pos_left _ hp
    omega
  have htℓ : ρ + 1 ≤ hLen p m B := by omega
  refine ⟨ρ, hρr, hqρ, ?_⟩
  obtain ⟨c, hc, hdep⟩ := exists_dependence_of_rank_le ((Hmat FS m B y).map (aeval FS.γ)) le_rfl htℓ
  refine ⟨c, hc, fun i => ?_⟩
  have := hdep i
  simp only [Hmat_map_aeval hB hm hy, Fin.val_castLE] at this
  exact this

end ExplicitTables

end LatticePrepro

open LatticePrepro
open Polynomial Matrix
open LatticePrepro.ExplicitTables
variable {p : ℕ} [Fact p.Prime] {d δ : ℕ} (FS : FieldSetup p d δ) (m B : ℕ)
variable {FS m B}
theorem solution (hB : 2 ≤ B) (hm : 1 ≤ m)
    (hΔ : 4 * degBound p m B δ < Fintype.card FS.𝕊) {y : Coord FS m → ZMod p}
    (hy : constraintFun FS m B y = 0) (hw : 2 * hammingNorm y < B ^ m * Fintype.card FS.𝕊) :
    ∃ t : ℕ, t < B ^ m ∧ Fintype.card FS.𝕊 * t ≤ 2 * hammingNorm y ∧
      ∃ c : Fin (t + 1) → FS.K, c ≠ 0 ∧
        ∀ i : Fin (hLen p m B), ∑ j, c j * mom FS m B y (i.val + j.val) = 0 :=
  @LatticePrepro.ExplicitTables.soundness_setup p _ d δ FS m B hB hm hΔ y hy hw
