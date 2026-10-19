-- Prove2me | solution 1 for OAI.Erdos3.exists_physical_stack_record_descent_s2
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T05:54:12.089001+00:00
-- url     : https://prove2.me/submissions/99de4d4d-14ff-40a4-830a-66409d9d1279

import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B165
import Definitions.Def_OAIE3v2B180
import Definitions.Def_OAIE3v2B191

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueSliceCountingCost
namespace OAI

section

namespace Erdos3

theorem scalarResidue_card_mul_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r ≤ b - a + r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := Int.Ico_filter_modEq_card a b hr v
  have hcQ := congrArg (fun n : ℤ => (n : ℚ)) hc
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hcQ
  have hn : (0 : ℚ) ≤ ((b - a : ℤ) : ℚ) / r :=
    div_nonneg (by exact_mod_cast sub_nonneg.mpr hab) hrQ.le
  have hbound : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) ≤
      ((b - a : ℤ) : ℚ) / r + 1 := by
    rw [hcQ]
    apply max_le
    · have hx := Int.ceil_lt_add_one (((b : ℚ) - v) / r)
      have hy := Int.le_ceil (((a : ℚ) - v) / r)
      have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
        push_cast
        ring
      linarith
    · linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r + 1) * r = (b - a : ℤ) + (r : ℚ) := by
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_real_le (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) ≤
      ((b - a : ℤ) : ℝ) / r + 1 := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have h := scalarResidue_card_mul_le a b r v hab hr
  have hR : ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r ≤
      ((b - a : ℤ) : ℝ) + r := by exact_mod_cast h
  have heq : ((b - a : ℤ) : ℝ) + r = (((b - a : ℤ) : ℝ) / r + 1) * r := by
    field_simp
  rw [heq] at hR
  exact (mul_le_mul_iff_left₀ hrR).mp hR

end Erdos3

end

section

namespace Erdos3

theorem scalarResidue_card_mul_ge (a b r v : ℤ) (hr : 0 < r) :
    b - a - r ≤ ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℤ) * r := by
  have hrQ : (0 : ℚ) < r := by exact_mod_cast hr
  have hc := congrArg (fun n : ℤ => (n : ℚ)) (Int.Ico_filter_modEq_card a b hr v)
  simp only [Int.cast_natCast, Int.cast_max, Int.cast_sub, Int.cast_zero] at hc
  have hbound : ((b - a : ℤ) : ℚ) / r - 1 ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℚ) := by
    rw [hc]
    apply le_trans _ (le_max_left _ _)
    have hx := Int.le_ceil (((b : ℚ) - v) / r)
    have hy := Int.ceil_lt_add_one (((a : ℚ) - v) / r)
    have heq : ((b : ℚ) - v) / r - ((a : ℚ) - v) / r = ((b - a : ℤ) : ℚ) / r := by
      push_cast
      ring
    linarith
  have hm := mul_le_mul_of_nonneg_right hbound hrQ.le
  have heq : (((b - a : ℤ) : ℚ) / r - 1) * r = ((b - a - r : ℤ) : ℚ) := by
    push_cast
    field_simp
  rw [heq] at hm
  exact_mod_cast hm

theorem scalarResidue_card_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) -
      ((b - a : ℤ) : ℝ) / r| ≤ 1 := by
  have hu := scalarResidue_card_real_le a b r v hab hr
  have hl : ((b - a - r : ℤ) : ℝ) ≤
      ((Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card : ℝ) * r := by
    exact_mod_cast scalarResidue_card_mul_ge a b r v hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have heq : (((b - a : ℤ) : ℝ) / r - 1) * r = ((b - a - r : ℤ) : ℝ) := by
    push_cast
    field_simp
  rw [← heq] at hl
  have hlow := (mul_le_mul_iff_left₀ hrR).mp hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_eq_card (a b r v : ℤ) (hr : 0 < r) :
    residueIndexLength a b r v =
      (Finset.filter (fun x => x ≡ v [ZMOD r]) (Finset.Ico a b)).card := by
  rw [residueInterval_eq_map a b r v hr, Finset.card_map, Int.card_Ico]
  omega

theorem residueIndexLength_absolute_error (a b r v : ℤ) (hab : a ≤ b) (hr : 0 < r) :
    |(residueIndexLength a b r v : ℝ) - ((b - a : ℤ) : ℝ) / (r : ℝ)| ≤ 1 := by
  rw [residueIndexLength_eq_card a b r v hr]
  exact scalarResidue_card_absolute_error a b r v hab hr

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_ge_of_width (a b r v : ℤ) (hr : 0 < r)
    (B : ℝ) (hB : 0 ≤ B) (hwidth : (r : ℝ) * (B + 1) ≤ ((b - a : ℤ) : ℝ)) :
    B ≤ (residueIndexLength a b r v : ℝ) := by
  have hr' : (0 : ℝ) < r := by exact_mod_cast hr
  have hwidthpos : (0 : ℝ) < ((b - a : ℤ) : ℝ) :=
    (mul_pos hr' (by linarith : 0 < B + 1)).trans_le hwidth
  have hab : a ≤ b := by
    have h : (0 : ℤ) ≤ b - a := by exact_mod_cast hwidthpos.le
    omega
  have hlower := (abs_le.mp (residueIndexLength_absolute_error a b r v hab hr)).1
  have hratio : B + 1 ≤ ((b - a : ℤ) : ℝ) / (r : ℝ) :=
    (le_div_iff₀ hr').mpr (by simpa only [mul_comm] using hwidth)
  linarith

end Erdos3

end

section

namespace Erdos3

theorem residueIndexLength_half_width (a v : ℤ) (N r : ℕ) (hr : 0 < r)
    (hwidth : 2 * (r : ℝ) ≤ (N : ℝ)) :
    0 < residueIndexLength a (a + N) r v ∧
    (N : ℝ) / 2 ≤ (r : ℝ) * (residueIndexLength a (a + N) r v : ℝ) := by
  have hrz : (0 : ℤ) < r := by exact_mod_cast hr
  have hrr : (0 : ℝ) < r := by exact_mod_cast hr
  have hlength := residueIndexLength_ge_of_width a (a + N) r v hrz 1 (by norm_num)
    (by simpa only [add_sub_cancel_left, Int.cast_natCast] using (show (r : ℝ) * (1 + 1) ≤ (N : ℝ) by linarith))
  have herror := residueIndexLength_absolute_error a (a + N) r v (by omega) hrz
  simp only [add_sub_cancel_left, Int.cast_natCast] at herror
  have hlo := (abs_le.mp herror).1
  have hmul := mul_le_mul_of_nonneg_left hlo hrr.le
  have hdiv : (r : ℝ) * ((N : ℝ) / r) = (N : ℝ) := by field_simp
  refine ⟨?_, ?_⟩
  · exact_mod_cast (show (0 : ℝ) < (residueIndexLength a (a + N) r v : ℝ) by linarith)
  · nlinarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Nilpotent.NiltestAffineProjection
namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_eq_of_orbit_eq (T U : D.Niltest w) (h : T.orbit = U.orbit)
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    T.symbol b ω hF = U.symbol b ω hF := by
  unfold symbol
  apply congrArg (D.filtration.realPolynomialSymbolHom b ω hF w)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : D.filtration.realification.PolynomialOrbit w => o.log) h

theorem affinePullback_orbit_eq_of_orbit_eq [Fintype τ]
    (T U : D.Niltest (fun _ : σ => 1)) (h : T.orbit = U.orbit)
    (A : σ → τ → ℤ) (b : σ → ℤ) :
    (T.affinePullback A b).orbit = (U.affinePullback A b).orbit := by
  change D.filtration.realification.polynomialOrbitSubstitute _ _ T.orbit =
    D.filtration.realification.polynomialOrbitSubstitute _ _ U.orbit
  rw [h]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.CommonStrideResidueGeometry
namespace OAI

section

namespace Erdos3

theorem commonStridePoint_index_of_modEq {I : Type*} (c : I → ℤ) (m : ℕ) (y : I → ℤ)
    (hy : ∀ i, y i ≡ c i [ZMOD (m : ℤ)]) :
    commonStridePoint c m (commonStrideIndex c m y) = y := by
  funext i
  have hd := Int.modEq_iff_dvd.mp (hy i).symm
  change c i + (m : ℤ) * ((y i - c i) / (m : ℤ)) = y i
  rw [mul_comm, Int.ediv_mul_cancel hd]
  omega

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueStrideRebase
namespace OAI

section

namespace Erdos3

theorem scalarAffinePolynomial_comp {σ : Type*} (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) (i : σ) :
    MvPolynomial.aeval (scalarAffinePolynomial r₁ h₁) (scalarAffinePolynomial r₀ h₀ i) =
      scalarAffinePolynomial (r₀ * r₁) (fun j => r₀ * h₁ j + h₀ j) i := by
  simp only [scalarAffinePolynomial, map_add, map_mul, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, MvPolynomial.algebraMap_eq]
  ring

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_comp_orbit (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ : ℚ) (h₀ h₁ : σ → ℚ) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback r₁ h₁).orbit =
      (T.scalarAffinePullback (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i)).orbit := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (scalarAffinePolynomial r₁ h₁)
      (VectorPolynomial.substitute (scalarAffinePolynomial r₀ h₀) T.orbit.log) =
    VectorPolynomial.substitute (scalarAffinePolynomial (r₀ * r₁) (fun i => r₀ * h₁ i + h₀ i))
      T.orbit.log
  rw [VectorPolynomial.substitute_comp]
  simp only [scalarAffinePolynomial_comp]

theorem scalarAffinePullback_comp_orbit_of_eq (T : D.Niltest (fun _ : σ => 1))
    (r₀ r₁ a : ℚ) (h₀ h₁ shift : σ → ℚ) (hr : r₀ * a = r₁)
    (hh : ∀ i, r₀ * shift i + h₀ i = h₁ i) :
    ((T.scalarAffinePullback r₀ h₀).scalarAffinePullback a shift).orbit =
      (T.scalarAffinePullback r₁ h₁).orbit := by
  rw [T.scalarAffinePullback_comp_orbit, hr, funext hh]

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem residue_refinement_offset_identity {σ : Type*}
    (u v : σ → ℤ) (M : ℕ) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (i : σ) :
    (M : ℚ) * (commonStrideIndex u M v i : ℚ) + (u i : ℚ) = (v i : ℚ) := by
  have h := congrFun (commonStridePoint_index_of_modEq u M v hv) i
  change u i + (M : ℤ) * commonStrideIndex u M v i = v i at h
  exact_mod_cast (show (M : ℤ) * commonStrideIndex u M v i + u i = v i by omega)

theorem residue_refinement_parameter_bounds {σ : Type*}
    (u v : σ → ℤ) {M N : ℕ} (hM : 0 < M) (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) (A B : σ → ℝ)
    (hoffset : ∀ i, |(v i : ℝ) - (u i : ℝ)| ≤ (M : ℝ) * A i)
    (hspan : ∀ i, (N : ℝ) * B i ≤ (M : ℝ) * A i) :
    (∀ i, |(commonStrideIndex u M v i : ℝ)| ≤ A i) ∧
    (∀ i, |((N / M : ℕ) : ℝ)| * B i ≤ A i) := by
  have hMr : 0 < (M : ℝ) := by exact_mod_cast hM
  have hscale : (M : ℝ) * (N / M : ℕ) = N := by exact_mod_cast Nat.mul_div_cancel' hMN
  constructor
  · intro i
    have hshift : (M : ℝ) * (commonStrideIndex u M v i : ℝ) = (v i : ℝ) - (u i : ℝ) := by
      have h := residue_refinement_offset_identity u v M hv i
      have hh : (M : ℝ) * (commonStrideIndex u M v i : ℝ) + (u i : ℝ) = (v i : ℝ) := by
        exact_mod_cast h
      linarith
    apply (mul_le_mul_iff_right₀ hMr).mp
    calc
      (M : ℝ) * |(commonStrideIndex u M v i : ℝ)| =
          |(M : ℝ) * (commonStrideIndex u M v i : ℝ)| := by rw [abs_mul, abs_of_pos hMr]
      _ = |(v i : ℝ) - (u i : ℝ)| := by rw [hshift]
      _ ≤ (M : ℝ) * A i := hoffset i
  · intro i
    apply (mul_le_mul_iff_right₀ hMr).mp
    calc
      (M : ℝ) * (|((N / M : ℕ) : ℝ)| * B i) = ((M : ℝ) * (N / M : ℕ)) * B i := by
        rw [abs_of_nonneg (Nat.cast_nonneg _)]; ring
      _ = (N : ℝ) * B i := by rw [hscale]
      _ ≤ (M : ℝ) * A i := hspan i

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_refinement_orbit (T : D.Niltest (fun _ : σ => 1))
    (u v : σ → ℤ) {M N : ℕ} (hMN : M ∣ N)
    (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)]) :
    ((T.scalarAffinePullback (M : ℚ) (fun i => (u i : ℚ))).scalarAffinePullback
      (N / M : ℕ) (fun i => (commonStrideIndex u M v i : ℚ))).orbit =
      (T.scalarAffinePullback (N : ℚ) (fun i => (v i : ℚ))).orbit := by
  apply T.scalarAffinePullback_comp_orbit_of_eq
  · exact_mod_cast Nat.mul_div_cancel' hMN
  · exact residue_refinement_offset_identity u v M hv

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem integerAffinePolynomial_residue_scalar {σ : Type*} [Fintype σ] [DecidableEq σ]
    (J : ℕ) (shift : σ → ℤ) :
    integerAffinePolynomial (residueStepMatrix (fun _ : σ => J)) shift =
      scalarAffinePolynomial (J : ℚ) (fun i => (shift i : ℚ)) := by
  funext i
  simp [integerAffinePolynomial, residueStepMatrix, scalarAffinePolynomial, apply_ite, ite_mul]

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

theorem residue_scalar_affine_orbit (T : D.Niltest (fun _ : σ => 1))
    (J : ℕ) (shift : σ → ℤ) :
    (T.affinePullback (residueStepMatrix (fun _ : σ => J)) shift).orbit =
      (T.scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ))).orbit := by
  apply Subtype.ext
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.substitute (integerAffinePolynomial (residueStepMatrix (fun _ : σ => J)) shift)
      T.orbit.log = VectorPolynomial.substitute (scalarAffinePolynomial (J : ℚ)
        (fun i => (shift i : ℚ))) T.orbit.log
  rw [integerAffinePolynomial_residue_scalar]

theorem residue_scalar_affine_symbol (T : D.Niltest (fun _ : σ => 1))
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (J : ℕ) (shift : σ → ℤ) :
    (T.affinePullback (residueStepMatrix (fun _ : σ => J)) shift).symbol D.basis ω hF =
      (T.scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ))).symbol D.basis ω hF :=
  (T.affinePullback (residueStepMatrix (fun _ : σ => J)) shift).symbol_eq_of_orbit_eq
    (T.scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ)))
    (T.residue_scalar_affine_orbit J shift) D.basis ω hF

end RationalFilteredNilmanifold.Niltest

end Erdos3

end

section

namespace Erdos3

theorem physical_box_anchor_bounds {σ : Type*}
    (lo lo' u v : σ → ℤ) (N N' : σ → ℕ)
    (hu : ∀ i, lo i ≤ u i ∧ u i < lo i + N i)
    (hsub : ∀ i, lo i ≤ lo' i ∧ lo' i + N' i ≤ lo i + N i)
    (hv : ∀ i, lo' i ≤ v i ∧ v i < lo' i + N' i) :
    (∀ i, |(v i : ℝ) - (u i : ℝ)| ≤ (N i : ℝ)) ∧
    (∀ i, N' i ≤ N i) := by
  constructor
  · intro i
    have hleft : -(N i : ℤ) ≤ v i - u i := by
      have := hu i
      have := hsub i
      have := hv i
      omega
    have hright : v i - u i ≤ (N i : ℤ) := by
      have := hu i
      have := hsub i
      have := hv i
      omega
    exact abs_le.mpr ⟨by exact_mod_cast hleft, by exact_mod_cast hright⟩
  · intro i
    have := hsub i
    omega

theorem anchored_residue_refinement_bounds {σ : Type*}
    (lo lo' u v : σ → ℤ) (N N' : σ → ℕ) {M M' : ℕ}
    (hM : 0 < M) (hM' : 0 < M') (hdiv : M ∣ M')
    (hcompat : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hu : ∀ i, lo i ≤ u i ∧ u i < lo i + N i)
    (hsub : ∀ i, lo i ≤ lo' i ∧ lo' i + N' i ≤ lo i + N i)
    (hv : ∀ i, lo' i ≤ v i ∧ v i < lo' i + N' i)
    (hN' : ∀ i, 0 < N' i) :
    let A : σ → ℝ := fun i => (N i : ℝ) / M
    let B : σ → ℝ := fun i => (N' i : ℝ) / M'
    (∀ i, 0 < B i) ∧
    (∀ i, |(commonStrideIndex u M v i : ℝ)| ≤ A i) ∧
    (∀ i, |((M' / M : ℕ) : ℝ)| * B i ≤ A i) ∧
    (∀ i, (v i : ℝ) - (M' : ℝ) * B i ≤ (lo' i : ℝ) ∧
      (lo' i : ℝ) + (N' i : ℝ) ≤ (v i : ℝ) + (M' : ℝ) * B i) := by
  intro A B
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hM'r : (0 : ℝ) < M' := by exact_mod_cast hM'
  have hmul : ∀ i, (M : ℝ) * A i = (N i : ℝ) := by
    intro i
    dsimp only [A]
    field_simp
  have hmul' : ∀ i, (M' : ℝ) * B i = (N' i : ℝ) := by
    intro i
    dsimp only [B]
    field_simp
  obtain ⟨hoffset, hlength⟩ := physical_box_anchor_bounds lo lo' u v N N' hu hsub hv
  have hparams := residue_refinement_parameter_bounds u v hM hdiv hcompat A B
    (fun i => by simpa only [hmul] using hoffset i)
    (fun i => by simpa only [hmul, hmul'] using (show (N' i : ℝ) ≤ (N i : ℝ) by exact_mod_cast hlength i))
  refine ⟨fun i => div_pos (by exact_mod_cast hN' i) hM'r, hparams.1, hparams.2, ?_⟩
  intro i
  rw [hmul']
  have hlow : (lo' i : ℝ) ≤ (v i : ℝ) := by exact_mod_cast (hv i).1
  have hhigh : (v i : ℝ) < (lo' i : ℝ) + (N' i : ℝ) := by exact_mod_cast (hv i).2
  constructor <;> linarith

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.HalfResidueDescent
namespace OAI

section

namespace Erdos3

theorem exists_residue_descent_precision (C : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ p : ℝ, 0 ≤ p → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → Δ⁻¹ ≤ Real.exp p →
      ∃ ε δ : ℝ, 0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
        ε⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧ δ⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧
        8 * ε + 2 * (Real.exp ((p + 2) ^ C) * δ) = Δ / 2 := by
  let B : Polynomial ℕ := (Polynomial.X + 2) ^ C + Polynomial.X + Polynomial.C 32
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget B
  refine ⟨K, hK, ?_⟩
  intro p hp Δ hΔ hΔone hΔinv
  let E := Real.exp ((p + 2) ^ C)
  let ε := Δ / 32
  let δ := Δ / (8 * E)
  have hE : 0 < E := Real.exp_pos _
  have hEone : 1 ≤ E := Real.one_le_exp (pow_nonneg (by linarith) _)
  have hε : 0 < ε := div_pos hΔ (by norm_num)
  have hδ : 0 < δ := div_pos hΔ (mul_pos (by norm_num) hE)
  have htotal : (p + 2) ^ C + p + 32 ≤ (p + 2) ^ K := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  have hεinv : ε⁻¹ = 32 * Δ⁻¹ := by
    change (Δ / 32)⁻¹ = 32 * Δ⁻¹
    rw [inv_div, div_eq_mul_inv]
  have hδinv : δ⁻¹ = 8 * E * Δ⁻¹ := by
    change (Δ / (8 * E))⁻¹ = 8 * E * Δ⁻¹
    rw [inv_div, div_eq_mul_inv]
  have h32 : (32 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hεbound : ε⁻¹ ≤ Real.exp ((p + 2) ^ K) := by
    rw [hεinv]
    calc
      32 * Δ⁻¹ ≤ 32 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 32 * Real.exp p := mul_le_mul_of_nonneg_right h32 (Real.exp_nonneg _)
      _ = Real.exp (32 + p) := (Real.exp_add _ _).symm
      _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith [pow_nonneg (by linarith : 0 ≤ p + 2) C])
  have hδbound : δ⁻¹ ≤ Real.exp ((p + 2) ^ K) := by
    rw [hδinv]
    calc
      8 * E * Δ⁻¹ ≤ 8 * E * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by positivity)
      _ ≤ Real.exp 8 * E * Real.exp p := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h8 hE.le) (Real.exp_nonneg _)
      _ = Real.exp (8 + (p + 2) ^ C + p) := by
        dsimp only [E]
        rw [← Real.exp_add, ← Real.exp_add]
      _ ≤ _ := Real.exp_le_exp.mpr (by linarith)
  have hcancel : E * δ = Δ / 8 := by
    dsimp only [δ]
    field_simp
  refine ⟨ε, δ, hε, ?_, hδ, ?_, hεbound, hδbound, ?_⟩
  · dsimp only [ε]
    linarith
  · apply (div_le_one (mul_pos (by norm_num) hE)).mpr
    linarith
  · change 8 * ε + 2 * (E * δ) = Δ / 2
    rw [hcancel]
    dsimp only [ε]
    ring

end Erdos3

end

section

namespace Erdos3

theorem exists_residue_event_descent_precision (C : ℕ) :
    ∃ K : ℕ, 2 ≤ K ∧ ∀ p : ℝ, 0 ≤ p → ∀ Δ : ℝ,
      0 < Δ → Δ ≤ 1 → Δ⁻¹ ≤ Real.exp p →
      ∃ rho q ε δ : ℝ,
        p + 16 ≤ q ∧ verticalDecompositionBudget (p + 16) ≤ q ∧ q ≤ (p + 2) ^ K ∧
        0 < rho ∧ rho⁻¹ ≤ Real.exp (p + 16) ∧
        0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
        ε⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧ δ⁻¹ ≤ Real.exp ((p + 2) ^ K) ∧
        2 * (2 * rho + Real.exp (verticalDecompositionBudget (p + 16) - q)) ≤ Δ / 2 ∧
        8 * ε + 2 * (Real.exp (((p + 16) + 2) ^ C) * δ) = Δ / 4 := by
  obtain ⟨C₀, _, hvertical⟩ := exists_verticalDecompositionBudget_bound
  obtain ⟨K₀, _, hprecision⟩ := exists_residue_descent_precision C
  let P : Polynomial ℕ := (Polynomial.X + 18) ^ K₀ +
    (Polynomial.X + Polynomial.C (16 + C₀)) ^ C₀ + Polynomial.X + 32
  obtain ⟨K, hK, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨K, hK, ?_⟩
  intro p hp Δ hΔ hΔone hΔinv
  have hp16 : 0 ≤ p + 16 := by linarith
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hdouble : (Δ / 2)⁻¹ ≤ Real.exp (p + 16) := by
    rw [inv_div, div_eq_mul_inv]
    calc
      2 * Δ⁻¹ ≤ 2 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right (by linarith) (Real.exp_nonneg _)
      _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, herror⟩ :=
    hprecision (p + 16) hp16 (Δ / 2) (by positivity) (by linarith) hdouble
  let rho := Δ / 16
  let q := verticalDecompositionBudget (p + 16) + p + 32
  have hfreq0 : 0 ≤ verticalDecompositionBudget (p + 16) :=
    verticalDecompositionBudget_nonneg hp16
  have hpoly : (p + 18) ^ K₀ + (p + (16 + C₀ : ℕ)) ^ C₀ + p + 32 ≤ (p + 2) ^ K := by
    simpa [P, Polynomial.eval₂_pow] using hbudget p hp
  have hfreq : verticalDecompositionBudget (p + 16) ≤ (p + (16 + C₀ : ℕ)) ^ C₀ := by
    simpa [Nat.cast_add, Nat.cast_ofNat, add_assoc] using hvertical (p + 16) hp16
  have hpow : ((p + 16) + 2) ^ K₀ ≤ (p + 2) ^ K := by
    have hother : 0 ≤ (p + (16 + C₀ : ℕ)) ^ C₀ := by positivity
    have heq : (p + 16) + 2 = p + 18 := by ring
    rw [heq]
    linarith
  have hq : q ≤ (p + 2) ^ K := by
    have hother : 0 ≤ (p + 18) ^ K₀ := by positivity
    dsimp only [q]
    linarith
  have hrho : rho⁻¹ ≤ Real.exp (p + 16) := by
    change (Δ / 16)⁻¹ ≤ Real.exp (p + 16)
    rw [inv_div, div_eq_mul_inv]
    calc
      16 * Δ⁻¹ ≤ 16 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right h16 (Real.exp_nonneg _)
      _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
  have hsmall : Real.exp (-p) ≤ Δ := by
    rw [Real.exp_neg]
    exact (inv_le_comm₀ hΔ (Real.exp_pos p)).mp hΔinv
  have h32 : (8 : ℝ) ≤ Real.exp 32 := by linarith [Real.add_one_le_exp (32 : ℝ)]
  have htail : Real.exp (-32 : ℝ) ≤ 1 / 8 := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 8) h32
  have htailbound : Real.exp (verticalDecompositionBudget (p + 16) - q) ≤ Δ / 8 := by
    have heq : verticalDecompositionBudget (p + 16) - q = -p + (-32) := by
      dsimp only [q]
      ring
    rw [heq, Real.exp_add]
    calc
      Real.exp (-p) * Real.exp (-32) ≤ Δ * (1 / 8) :=
        mul_le_mul hsmall htail (Real.exp_nonneg _) hΔ.le
      _ = _ := by ring
  refine ⟨rho, q, ε, δ, ?_, ?_, hq, by dsimp only [rho]; positivity, hrho,
    hε, hεhalf, hδ, hδone, hεbound.trans (Real.exp_le_exp.mpr hpow),
    hδbound.trans (Real.exp_le_exp.mpr hpow), ?_, ?_⟩
  · dsimp only [q]
    linarith
  · dsimp only [q]
    linarith
  · dsimp only [rho]
    linarith
  · linarith

end Erdos3

end

section

namespace Erdos3

theorem exists_separated_residue_precision :
    ∃ Kevent : ℕ, 2 ≤ Kevent ∧ ∀ C : ℕ, ∃ Kfreeze : ℕ, 2 ≤ Kfreeze ∧
      ∀ p : ℝ, 0 ≤ p → ∀ Δ : ℝ, 0 < Δ → Δ ≤ 1 → Δ⁻¹ ≤ Real.exp p →
      ∃ rho q : ℝ,
        p + 16 ≤ q ∧ verticalDecompositionBudget (p + 16) ≤ q ∧ q ≤ (p + 2) ^ Kevent ∧
        0 < rho ∧ rho⁻¹ ≤ Real.exp (p + 16) ∧
        2 * (2 * rho + Real.exp (verticalDecompositionBudget (p + 16) - q)) ≤ Δ / 2 ∧
        ∀ work : ℝ, p + 16 ≤ work → ∃ ε δ : ℝ,
          0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
          ε⁻¹ ≤ Real.exp ((work + 2) ^ Kfreeze) ∧ δ⁻¹ ≤ Real.exp ((work + 2) ^ Kfreeze) ∧
          8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) = Δ / 4 := by
  obtain ⟨Kevent, hKevent, hevent⟩ := exists_residue_event_descent_precision 0
  refine ⟨Kevent, hKevent, ?_⟩
  intro C
  obtain ⟨Kfreeze, hKfreeze, hfreeze⟩ := exists_residue_descent_precision C
  refine ⟨Kfreeze, hKfreeze, ?_⟩
  intro p hp Δ hΔ hΔone hΔinv
  obtain ⟨rho, q, _, _, hpq, hfreq, hq, hrho, hrhop, _, _, _, _, _, _, hprojection, _⟩ :=
    hevent p hp Δ hΔ hΔone hΔinv
  refine ⟨rho, q, hpq, hfreq, hq, hrho, hrhop, hprojection, ?_⟩
  intro work hwork
  have h16 : (2 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hdouble : (Δ / 2)⁻¹ ≤ Real.exp work := by
    rw [inv_div, div_eq_mul_inv]
    calc
      2 * Δ⁻¹ ≤ 2 * Real.exp p := mul_le_mul_of_nonneg_left hΔinv (by norm_num)
      _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right h16 (Real.exp_nonneg _)
      _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp work := Real.exp_le_exp.mpr hwork
  obtain ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, herror⟩ :=
    hfreeze work (by linarith) (Δ / 2) (by positivity) (by linarith) hdouble
  exact ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, by linarith⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Lattices.ResidueEventOrDescent
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem residuePairStep_const {σ : Type*} (J : ℕ) (flag : Bool) :
    residuePairStep (fun _ : σ => J) flag = fun _ => if flag then J else 1 := by
  cases flag <;> rfl

namespace RationalFilteredNilmanifold.Niltest

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)] {s d : ℕ}
  {D : RationalFilteredNilmanifold L s d}

theorem residue_scalar_composed_symbol (T : D.Niltest (fun _ : σ => 1))
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (r : ℚ) (h : σ → ℚ) (J : ℕ) (shift : σ → ℤ) :
    ((T.scalarAffinePullback r h).affinePullback (residueStepMatrix (fun _ : σ => J)) shift).symbol
        D.basis ω hF =
      (T.scalarAffinePullback (r * J) (fun i => r * (shift i : ℚ) + h i)).symbol D.basis ω hF := by
  rw [(T.scalarAffinePullback r h).residue_scalar_affine_symbol ω hF J shift]
  exact ((T.scalarAffinePullback r h).scalarAffinePullback (J : ℚ) (fun i => (shift i : ℚ))).symbol_eq_of_orbit_eq
    (T.scalarAffinePullback (r * J) (fun i => r * (shift i : ℚ) + h i))
    (T.scalarAffinePullback_comp_orbit r (J : ℚ) h (fun i => (shift i : ℚ))) D.basis ω hF

end RationalFilteredNilmanifold.Niltest

theorem ResiduePairDimensionDrop.scalar_record {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (h : σ → ℚ)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (M J : ℕ) (u v : σ → ℤ) (B : ℝ)
    (hevent : ResiduePairDimensionDrop D ω hF (T.scalarAffinePullback r h) W lo N M u v
      (fun _ => J) B) :
    ∃ (flag : Bool) (l : ℕ) (U : LieSubalgebra ℚ D.filtration.AssociatedGraded)
        (z : Fin d → D.filtration.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp B ∧
      Submodule.span ℚ (Set.range z) = U.toSubmodule ∧
      BasisGradedSubmodule (D.filtration.associatedGradedBasis D.basis ω hF) ω U.toSubmodule ∧
      (∀ i j, rationalLogHeight ((D.filtration.associatedGradedBasis D.basis ω hF).repr (z i) j) ≤ B) ∧
      finrank ℚ ↥(W ⊓ U) < finrank ℚ W ∧
      D.filtration.SymbolFactorizationIn D.basis ω hF
        (fun i => (residueIndexLength (lo i) (lo i + N i) (M * (if flag then J else 1) : ℕ)
          (residuePairValue u v flag i) : ℝ))
        ((T.scalarAffinePullback (r * (if flag then J else 1 : ℕ))
          (fun i => r * (commonStrideIndex u M (residuePairValue u v flag) i : ℚ) + h i)).symbol
            D.basis ω hF) B l U := by
  obtain ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩ := hevent
  rw [residuePairStep_const] at hfactor
  rw [T.residue_scalar_composed_symbol] at hfactor
  exact ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem ResiduePairDimensionDrop.of_orbit_eq {σ L : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T S : D.Niltest (fun _ : σ => 1)) (hTS : T.orbit = S.orbit)
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ) (B : ℝ)
    (hevent : ResiduePairDimensionDrop D ω hF T W lo N M u v J B) :
    ResiduePairDimensionDrop D ω hF S W lo N M u v J B := by
  obtain ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩ := hevent
  have horbit := T.affinePullback_orbit_eq_of_orbit_eq S hTS
    (residueStepMatrix (residuePairStep J flag)) (commonStrideIndex u M (residuePairValue u v flag))
  have hsymbol := (T.affinePullback (residueStepMatrix (residuePairStep J flag))
      (commonStrideIndex u M (residuePairValue u v flag))).symbol_eq_of_orbit_eq
    (S.affinePullback (residueStepMatrix (residuePairStep J flag))
      (commonStrideIndex u M (residuePairValue u v flag))) horbit D.basis ω hF
  rw [hsymbol] at hfactor
  exact ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.AnchoredEpochVisit
namespace OAI

section

namespace Erdos3

open Module NilpotentLieFiltration RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem FixedAffineEpochTransition.on_anchored_box
    {σ L K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing L] [LieAlgebra ℚ L] [LieRing K] [LieAlgebra ℚ K]
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)] {s d t e : ℕ}
    (D : RationalFilteredNilmanifold L s d)
    (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (T : D.Niltest (fun _ : σ => 1))
    (V : RationalFilteredNilmanifold K t e)
    (child : V.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (work cost : ℝ) (P C B : ℕ)
    (lo₀ u₀ : σ → ℤ) (N₀ : σ → ℕ) (M₀ : ℕ) (hM₀ : 0 < M₀)
    (hu₀ : ∀ i, lo₀ i ≤ u₀ i ∧ u₀ i < lo₀ i + N₀ i)
    (htransition : FixedAffineEpochTransition D ω hF W T
      (fun i => (N₀ i : ℝ) / M₀) V child work cost P C B)
    (p : ℝ) (hp : 0 ≤ p) (hpwork : p ≤ work)
    (lo u v : σ → ℤ) (N : σ → ℕ) (M : ℕ) (J : σ → ℕ) (hM : 0 < M)
    (hdiv : M₀ ∣ M) (hucompat : ∀ i, u i ≡ u₀ i [ZMOD (M₀ : ℤ)])
    (hu : ∀ i, lo i ≤ u i ∧ u i < lo i + N i)
    (hsub : ∀ i, lo₀ i ≤ lo i ∧ lo i + N i ≤ lo₀ i + N₀ i)
    (hN : ∀ i, 0 < N i)
    (S : D.Niltest (fun _ : σ => 1))
    (hS : S.orbit = D.filtration.realification.scalarAffineOrbitHom (M / M₀ : ℕ)
      (fun i => (commonStrideIndex u₀ M₀ u i : ℚ)) T.orbit)
    (hunit : S.UnitIntervalValued) (hcost : S.ComplexityLE p)
    (q rho : ℝ) (hpq : p ≤ q) (hσ : (Fintype.card σ : ℝ) ≤ q)
    (hfreq : verticalDecompositionBudget p ≤ q) (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp p)
    (hJ : ∀ i, 0 < J i) (hv : ∀ i, v i ≡ u i [ZMOD (M : ℤ)])
    (hcop : ∀ i, (M * (M * P)).Coprime (J i))
    (hsteplarge : ∀ i, ((M * J i : ℕ) : ℝ) * (Real.exp ((q + B) ^ B) + 1) ≤ (N i : ℝ))
    (Δ ε δ : ℝ) (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : ε < 1 / 2)
    (hprojection : 2 * (2 * rho + Real.exp (verticalDecompositionBudget p - q)) ≤ Δ / 2)
    (hfreezing : 8 * ε + 2 * (Real.exp ((work + 2) ^ C) * δ) ≤ Δ / 4)
    (hlarge : ∀ i, 8 ≤ δ * (N i : ℝ))
    (hcount : (∑ i, ((Nat.lcm M (M * P) * J i : ℕ) : ℝ) / (N i : ℝ)) ≤ δ * ε / 8)
    (hgap : Δ ≤ ‖residuePairMean S.eval lo N M u v J false - residuePairMean S.eval lo N M u v J true‖) :
    ResiduePairDimensionDrop D ω hF S W lo N M u v J ((q + B) ^ B) ∨
    AnchoredChildResidueComparison V
      (V.filtration.realification.scalarAffineOrbitHom (M / M₀ : ℕ)
        (fun i => (commonStrideIndex u₀ M₀ u i : ℚ)) child)
      cost (Δ / 4) δ lo N M P u v J := by
  obtain ⟨hA, hshift, hscale, hphysical⟩ := anchored_residue_refinement_bounds
    lo₀ lo u₀ u N₀ N hM₀ hM hdiv hucompat hu₀ hsub hu hN
  have h := htransition p hp hpwork ((M / M₀ : ℕ) : ℤ) (commonStrideIndex u₀ M₀ u)
    (fun i => (N i : ℝ) / M) hA hshift
    (fun i => by simpa only [Int.cast_natCast] using hscale i) S
    (by simpa only [Int.cast_natCast] using hS) hunit hcost q rho hpq hσ hfreq hrho hrhop
    lo N M hM u v J hJ hv hcop hsteplarge Δ ε δ hδ hδone hε hprojection hfreezing
    hlarge hphysical hcount hgap
  simpa only [Int.cast_natCast] using h

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Polynomial.ResidueDegreeZero
namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

theorem residue_pair_discrepancy_step_zero {σ K : Type*} [Fintype σ] [DecidableEq σ]
    [LieRing K] [LieAlgebra ℚ K] {e : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] K)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] K)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] K)] [T2Space (ℝ ⊗[ℚ] K)]
    (V : RationalFilteredNilmanifold K 0 e) (T : V.Niltest (fun _ : σ => 1))
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (u v : σ → ℤ) (J : σ → ℕ)
    (hbase : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun _ => (M : ℤ)) u))
    (hfine : Nonempty (IntegerResidueBox lo (fun i => lo i + N i) (fun i => (M * J i : ℕ)) v)) :
    ‖residuePairMean T.eval lo N M u v J false - residuePairMean T.eval lo N M u v J true‖ = 0 := by
  let := hbase
  let := hfine
  rw [residuePairMean_false, residuePairMean_true]
  simp only [residueBoxStrideValue, RationalFilteredNilmanifold.Niltest.eval_step_zero,
    Fintype.expect_const, sub_self, norm_zero]

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PhysicalEpochComparison
namespace OAI

section

namespace Erdos3

open Module
open scoped TensorProduct

universe u v

attribute [instance] PhysicalEpochSource.lieRing PhysicalEpochSource.lieAlgebra
  PhysicalEpochSource.topology PhysicalEpochSource.topologicalAddGroup
  PhysicalEpochSource.continuousSMul PhysicalEpochSource.t2Space

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem ResiduePairDimensionDrop.physical_record
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T S : D.Niltest (fun _ : σ => 1))
    (W : LieSubalgebra ℚ D.filtration.AssociatedGraded)
    (lo : σ → ℤ) (N : σ → ℕ) (m a J : ℕ) (hm : 0 < m) (ha : 0 < a) (hJ : 0 < J)
    (u v : σ → ℤ) (B : ℝ)
    (hS : S.orbit = (T.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))).orbit)
    (hv : ∀ i, v i ≡ u i [ZMOD (m * a : ℕ)])
    (hwide : ∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (N i : ℝ))
    (hevent : ResiduePairDimensionDrop D ω hF S W lo N (m * a) u v (fun _ => J) B) :
    ∃ r : EpochSymbolRecord D ω hF T,
      r.budget = B ∧ r.auxiliary = a ∧ r.modulus ∣ m * J ∧
      finrank ℚ ↥(W ⊓ r.fast) < finrank ℚ W ∧
      ∀ i, (N i : ℝ) / 2 ≤ ((r.modulus : ℝ) * r.auxiliary) * r.sides i := by
  have hevent' := hevent.of_orbit_eq D ω hF S
    (T.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))) hS W lo N (m * a) u v (fun _ => J) B
  obtain ⟨flag, l, U, z, hl, hlB, hz, hgraded, hheight, hdrop, hfactor⟩ :=
    hevent'.scalar_record D ω hF T (m * a : ℕ) (fun i => (u i : ℚ)) W lo N (m * a) J u v B
  let f : ℕ := if flag then J else 1
  have hf : 0 < f := by cases flag <;> simp only [f, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hfJ : f ≤ J := by cases flag <;> simp only [f, Bool.false_eq_true, ite_false, ite_true] <;> omega
  have hpair : ∀ i, residuePairValue u v flag i ≡ u i [ZMOD (m * a : ℕ)] := by
    cases flag
    · exact fun i => Int.ModEq.refl _
    · exact hv
  have hshift : (fun i => ((m * a : ℕ) : ℚ) *
      (commonStrideIndex u (m * a) (residuePairValue u v flag) i : ℚ) + (u i : ℚ)) =
      (fun i => (residuePairValue u v flag i : ℚ)) :=
    funext (residue_refinement_offset_identity u (residuePairValue u v flag) (m * a) hpair)
  have hscale : ((m * a : ℕ) : ℚ) * f = ((m * f : ℕ) : ℚ) * a := by push_cast; ring
  change D.filtration.SymbolFactorizationIn D.basis ω hF
    (fun i => (residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ)
      (residuePairValue u v flag i) : ℝ))
    ((T.scalarAffinePullback (((m * a : ℕ) : ℚ) * f)
      (fun i => ((m * a : ℕ) : ℚ) * (commonStrideIndex u (m * a) (residuePairValue u v flag) i : ℚ) + (u i : ℚ))).symbol
      D.basis ω hF) B l U at hfactor
  rw [hscale, hshift] at hfactor
  have hlen : ∀ i, 0 < residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ)
        (residuePairValue u v flag i) ∧
      (N i : ℝ) / 2 ≤ ((m * a * f : ℕ) : ℝ) *
        (residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ) (residuePairValue u v flag i) : ℝ) := by
    intro i
    apply residueIndexLength_half_width (lo i) (residuePairValue u v flag i) (N i) (m * a * f)
      (Nat.mul_pos (Nat.mul_pos hm ha) hf)
    have hmf : ((m * a * f : ℕ) : ℝ) ≤ (m * a * J : ℕ) := by
      exact_mod_cast Nat.mul_le_mul_left (m * a) hfJ
    linarith [hwide i]
  let r : EpochSymbolRecord D ω hF T := {
    fast := U
    spanning := z
    budget := B
    denominator := l
    modulus := m * f
    auxiliary := a
    shift := fun i => (residuePairValue u v flag i : ℚ)
    sides := fun i => (residueIndexLength (lo i) (lo i + N i) (m * a * f : ℕ)
      (residuePairValue u v flag i) : ℝ)
    denominator_pos := hl
    modulus_pos := Nat.mul_pos hm hf
    auxiliary_pos := ha
    sides_pos := fun i => by exact_mod_cast (hlen i).1
    denominator_le := hlB
    span_eq := hz
    graded := hgraded
    height_le := hheight
    factorization := hfactor }
  refine ⟨r, rfl, rfl, ?_, hdrop, ?_⟩
  · change m * f ∣ m * J
    cases flag <;> simp [f]
  · intro i
    change (N i : ℝ) / 2 ≤ (((m * f : ℕ) : ℝ) * a) * _
    have heq : ((m * f : ℕ) : ℝ) * a = (m * a * f : ℕ) := by push_cast; ring
    rw [heq]
    exact (hlen i).2

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem EpochRecordHistory.extend_of_event
    {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i}))
    (T S : D.Niltest (fun _ : σ => 1)) (W : σ → ℝ) (p B : ℝ)
    (rs : List (EpochSymbolRecord D ω hF T)) (history : EpochRecordHistory rs)
    (hcontrolled : ∀ r ∈ rs, r.Controlled W p)
    (lo : σ → ℤ) (N : σ → ℕ) (m a J : ℕ) (hm : 0 < m) (ha : 0 < a) (hJ : 0 < J)
    (hdiv : ∀ r ∈ rs, r.modulus ∣ m) (hB : B ≤ p) (haB : (a : ℝ) ≤ Real.exp p)
    (u v : σ → ℤ)
    (hS : S.orbit = (T.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))).orbit)
    (hv : ∀ i, v i ≡ u i [ZMOD (m * a : ℕ)])
    (hwide : ∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (N i : ℝ))
    (hphysical : ∀ i, 2 * (Real.exp (-p) * W i) ≤ (N i : ℝ))
    (hevent : ResiduePairDimensionDrop D ω hF S (epochRecordIntersection rs)
      lo N (m * a) u v (fun _ => J) B) :
    ∃ r : EpochSymbolRecord D ω hF T,
      EpochRecordHistory (r :: rs) ∧
      (∀ t ∈ r :: rs, t.Controlled W p) ∧
      (∀ t ∈ r :: rs, t.modulus ∣ m * J) ∧
      finrank ℚ (epochRecordIntersection (r :: rs)) < finrank ℚ (epochRecordIntersection rs) := by
  obtain ⟨r, hrB, hra, hrdiv, hdrop, hspan⟩ := hevent.physical_record D ω hF T S
    (epochRecordIntersection rs) lo N m a J hm ha hJ u v B hS hv hwide
  have hr : r.Controlled W p := ⟨by simpa only [hrB] using hB,
    by simpa only [hra] using haB, fun i => by linarith [hspan i, hphysical i]⟩
  refine ⟨r, .cons history hdrop, ?_, ?_, ?_⟩
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hr
    · exact hcontrolled t ht
  · intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact hrdiv
    · exact (hdiv t ht).trans (dvd_mul_right m J)
  · change finrank ℚ ↥(r.fast ⊓ epochRecordIntersection rs) < _
    rw [inf_comm]
    exact hdrop

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v

namespace PhysicalEpochComparison

variable {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
  {base : PhysicalEpochSource.{u, v} σ s bound}

theorem base_nonempty (c : PhysicalEpochComparison base m a J gap) :
    Nonempty (IntegerResidueBox c.lower (fun i => c.lower i + c.sides i) (fun _ => (m * a : ℕ)) c.anchor) :=
  ⟨fun i => ⟨c.anchor i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (c.anchor_inside i), Int.ModEq.refl _⟩⟩⟩

theorem refined_nonempty (c : PhysicalEpochComparison base m a J gap) :
    Nonempty (IntegerResidueBox c.lower (fun i => c.lower i + c.sides i) (fun _ => (m * a * J : ℕ)) c.refined) :=
  ⟨fun i => ⟨c.refined i, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr (c.refined_inside i), Int.ModEq.refl _⟩⟩⟩

theorem impossible_at_zero {base : PhysicalEpochSource.{u, v} σ 0 bound}
    (c : PhysicalEpochComparison base m a J gap) : False := by
  have hzero := residue_pair_discrepancy_step_zero base.model c.test c.lower c.sides (m * a)
    c.anchor c.refined (fun _ => J) c.base_nonempty c.refined_nonempty
  have hgap := c.discrepancy
  rw [hzero] at hgap
  linarith [c.gap_pos]

end PhysicalEpochComparison

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalChildComparison
namespace OAI

section

namespace Erdos3

open scoped TensorProduct

universe u v

theorem quarter_discrepancy_inverse {gap p q : ℝ}
    (hgap : gap⁻¹ ≤ Real.exp p) (hpq : p + 16 ≤ q) :
    (gap / 4)⁻¹ ≤ Real.exp q := by
  have hfour : (4 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  rw [inv_div, div_eq_mul_inv]
  calc
    4 * gap⁻¹ ≤ 4 * Real.exp p := mul_le_mul_of_nonneg_left hgap (by norm_num)
    _ ≤ Real.exp 16 * Real.exp p := mul_le_mul_of_nonneg_right hfour (Real.exp_nonneg _)
    _ = Real.exp (p + 16) := by rw [← Real.exp_add]; congr 1; ring
    _ ≤ Real.exp q := Real.exp_le_exp.mpr hpq

theorem physical_comparison_of_anchored
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound : ℕ}
    (base : PhysicalEpochSource.{u, v} σ s bound) (m a J P : ℕ)
    (hm : 0 < m) (ha : 0 < a) (hJ : 0 < J) (hP : 0 < P)
    (lo : σ → ℤ) (N : σ → ℕ) (u z : σ → ℤ) (cost gap δ : ℝ)
    (hcost : cost ≤ base.incomingBudget) (hgap : 0 < gap) (hgapOne : gap ≤ 1)
    (hgapInv : gap⁻¹ ≤ Real.exp base.incomingBudget)
    (hcontained : ∀ i, base.lower i ≤ lo i ∧ lo i + N i ≤ base.lower i + base.sides i)
    (hcomparison : AnchoredChildResidueComparison base.model
      (base.fixedMap.scalarAffinePullback (m * a : ℕ) (fun i => (u i : ℚ))).orbit
      cost gap δ lo N (m * a) P u z (fun _ => J)) :
    ∃ c : PhysicalEpochComparison base m (a * P) J gap,
      (∀ i, lo i ≤ c.lower i ∧ c.lower i + c.sides i ≤ lo i + N i) ∧
      (∀ i, δ * (N i : ℝ) / 8 ≤ (c.sides i : ℝ) ∧ (c.sides i : ℝ) ≤ δ * (N i : ℝ) / 2) ∧
      (∀ i, c.anchor i ≡ u i [ZMOD (m * a : ℕ)]) ∧
      (∀ i, c.refined i ≡ z i [ZMOD (m * a * J : ℕ)]) := by
  obtain ⟨lo', N', w, z', U, hsub, hpos, hlength, hwInside, hzInside, hw, hz, hzw,
    _, _, hU, hunit, hUcost, hUgap⟩ := hcomparison
  have hQ : Nat.lcm (m * a) (m * a * P) = m * (a * P) := by
    rw [Nat.lcm_eq_right_iff_dvd.mpr (Nat.dvd_mul_right (m * a) P), Nat.mul_assoc]
  have hphysical := base.fixedMap.scalarAffinePullback_refinement_orbit u w
    (Nat.dvd_lcm_left (m * a) (m * a * P)) hw
  have hUphysical := hU.trans hphysical
  rw [hQ] at hUphysical hzw hUgap
  let c : PhysicalEpochComparison base m (a * P) J gap := {
    selected_pos := hm
    auxiliary_pos := Nat.mul_pos ha hP
    pending_pos := hJ
    lower := lo'
    sides := N'
    sides_pos := hpos
    contained := fun i => ⟨(hcontained i).1.trans (hsub i).1, (hsub i).2.trans (hcontained i).2⟩
    anchor := w
    refined := z'
    anchor_inside := hwInside
    refined_inside := hzInside
    compatible := hzw
    test := U
    orbit := hUphysical
    positive := hunit
    complexity := hUcost.mono hcost
    gap_pos := hgap
    gap_le_one := hgapOne
    gap_inverse := hgapInv
    discrepancy := hUgap }
  exact ⟨c, hsub, hlength, hw, hz⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.UniformPhysicalFrameConstruction
namespace OAI

section

namespace Erdos3

universe u v

theorem exists_physical_frame_precision :
    ∃ Ke : ℕ, 2 ≤ Ke ∧ ∀ C : ℕ, ∃ Kf : ℕ, 2 ≤ Kf ∧
      ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
        {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
        (frame : PhysicalEpochFrame base) (_c : PhysicalEpochComparison base m a J gap),
      frame.freezePower ≤ C → ∃ rho q ε δ : ℝ,
        base.incomingBudget + 16 ≤ q ∧ verticalDecompositionBudget (base.incomingBudget + 16) ≤ q ∧
        q ≤ (base.incomingBudget + 2) ^ Ke ∧ 0 < rho ∧ rho⁻¹ ≤ Real.exp (base.incomingBudget + 16) ∧
        0 < ε ∧ ε < 1 / 2 ∧ 0 < δ ∧ δ ≤ 1 ∧
        ε⁻¹ ≤ Real.exp ((frame.work + 2) ^ Kf) ∧ δ⁻¹ ≤ Real.exp ((frame.work + 2) ^ Kf) ∧
        2 * (2 * rho + Real.exp (verticalDecompositionBudget (base.incomingBudget + 16) - q)) ≤ gap / 2 ∧
        8 * ε + 2 * (Real.exp ((frame.work + 2) ^ frame.freezePower) * δ) ≤ gap / 4 := by
  obtain ⟨Ke, hKe, hprecision⟩ := exists_separated_residue_precision
  refine ⟨Ke, hKe, ?_⟩
  intro C
  obtain ⟨Kf, hKf, hstep⟩ := hprecision C
  refine ⟨Kf, hKf, ?_⟩
  intro σ _ _ s bound m a J gap base frame c hC
  obtain ⟨rho, q, hpq, hfreq, hq, hrho, hrhop, hprojection, hfreezing⟩ :=
    hstep base.incomingBudget base.incoming_nonneg gap c.gap_pos c.gap_le_one c.gap_inverse
  obtain ⟨ε, δ, hε, hεhalf, hδ, hδone, hεbound, hδbound, herror⟩ :=
    hfreezing frame.work frame.incoming_le_work
  refine ⟨rho, q, ε, δ, hpq, hfreq, hq, hrho, hrhop, hε, hεhalf, hδ, hδone,
    hεbound, hδbound, hprojection, ?_⟩
  have hwork : 0 ≤ frame.work := by linarith [frame.incoming_le_work, base.incoming_nonneg]
  have hpow : (frame.work + 2) ^ frame.freezePower ≤ (frame.work + 2) ^ C :=
    pow_le_pow_right₀ (by linarith) hC
  calc
    8 * ε + 2 * (Real.exp ((frame.work + 2) ^ frame.freezePower) * δ) ≤
        8 * ε + 2 * (Real.exp ((frame.work + 2) ^ C) * δ) := by gcongr
    _ = gap / 4 := herror

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct BigOperators

universe u v

theorem PhysicalEpochFrame.visit
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (hdiv : frame.modulus ∣ m * a)
    (hcompat : ∀ i, c.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)])
    (q rho ε δ : ℝ) (hpq : base.incomingBudget + 16 ≤ q)
    (hfreq : verticalDecompositionBudget (base.incomingBudget + 16) ≤ q)
    (hrho : 0 < rho) (hrhop : rho⁻¹ ≤ Real.exp (base.incomingBudget + 16))
    (hcop : (m * a * (m * a * frame.period)).Coprime J)
    (hsteplarge : ∀ i, ((m * a * J : ℕ) : ℝ) *
      (Real.exp ((q + frame.eventPower) ^ frame.eventPower) + 1) ≤ (c.sides i : ℝ))
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hε : ε < 1 / 2)
    (hprojection : 2 * (2 * rho + Real.exp (verticalDecompositionBudget (base.incomingBudget + 16) - q)) ≤ gap / 2)
    (hfreezing : 8 * ε + 2 * (Real.exp ((frame.work + 2) ^ frame.freezePower) * δ) ≤ gap / 4)
    (hlarge : ∀ i, 8 ≤ δ * (c.sides i : ℝ))
    (hcount : (∑ i, ((Nat.lcm (m * a) (m * a * frame.period) * J : ℕ) : ℝ) / (c.sides i : ℝ)) ≤ δ * ε / 8) :
    ResiduePairDimensionDrop base.model base.weights base.adapted c.test
      (epochRecordIntersection frame.state.records) c.lower c.sides (m * a) c.anchor c.refined
      (fun _ => J) ((q + frame.eventPower) ^ frame.eventPower) ∨
    ∃ next : PhysicalEpochComparison frame.child m (a * frame.period) J (gap / 4),
      (∀ i, c.lower i ≤ next.lower i ∧ next.lower i + next.sides i ≤ c.lower i + c.sides i) ∧
      (∀ i, δ * (c.sides i : ℝ) / 8 ≤ (next.sides i : ℝ) ∧ (next.sides i : ℝ) ≤ δ * (c.sides i : ℝ) / 2) ∧
      (∀ i, next.anchor i ≡ c.anchor i [ZMOD (m * a : ℕ)]) ∧
      (∀ i, next.refined i ≡ c.refined i [ZMOD (m * a * J : ℕ)]) := by
  have hparent := base.fixedMap.scalarAffinePullback_refinement_orbit frame.anchor c.anchor hdiv hcompat
  have hinput : c.test.orbit = base.model.filtration.realification.scalarAffineOrbitHom (m * a / frame.modulus : ℕ)
      (fun i => (commonStrideIndex frame.anchor frame.modulus c.anchor i : ℚ))
      (base.fixedMap.scalarAffinePullback (frame.modulus : ℚ) (fun i => (frame.anchor i : ℚ))).orbit :=
    c.orbit.trans hparent.symm
  have hresult := FixedAffineEpochTransition.on_anchored_box
    base.model base.weights base.adapted (epochRecordIntersection frame.state.records)
    (base.fixedMap.scalarAffinePullback (frame.modulus : ℚ) (fun i => (frame.anchor i : ℚ)))
    frame.child.model (frame.child.fixedMap.scalarAffinePullback (frame.modulus : ℚ) (fun i => (frame.anchor i : ℚ))).orbit
    frame.work frame.childCost frame.period frame.freezePower frame.eventPower
    base.lower frame.anchor base.sides frame.modulus frame.modulus_pos frame.anchor_inside frame.transition
    (base.incomingBudget + 16) (by linarith [base.incoming_nonneg]) frame.incoming_le_work
    c.lower c.anchor c.refined c.sides (m * a) (fun _ => J) (Nat.mul_pos c.selected_pos c.auxiliary_pos)
    hdiv hcompat c.anchor_inside c.contained c.sides_pos c.test hinput c.positive
    (c.complexity.mono (by linarith)) q rho hpq (base.coordinates_le.trans (by linarith))
    hfreq hrho hrhop (fun _ => c.pending_pos) c.compatible (fun _ => hcop) hsteplarge
    gap ε δ hδ hδone hε hprojection hfreezing hlarge hcount c.discrepancy
  rcases hresult with hevent | hchild
  · exact Or.inl hevent
  · have hchildOrbit := frame.child.fixedMap.scalarAffinePullback_refinement_orbit
      frame.anchor c.anchor hdiv hcompat
    have hchild' : AnchoredChildResidueComparison frame.child.model
        (frame.child.fixedMap.scalarAffinePullback (m * a : ℕ) (fun i => (c.anchor i : ℚ))).orbit
        frame.childCost (gap / 4) δ c.lower c.sides (m * a) frame.period c.anchor c.refined (fun _ => J) := by
      rw [← hchildOrbit]
      exact hchild
    exact Or.inr (physical_comparison_of_anchored frame.child m a J frame.period
      c.selected_pos c.auxiliary_pos c.pending_pos frame.period_pos c.lower c.sides c.anchor c.refined
      frame.childCost (gap / 4) δ frame.childCost_le (div_pos c.gap_pos (by norm_num)) (by linarith [c.gap_le_one])
      (quarter_discrepancy_inverse c.gap_inverse frame.incoming_le_child)
      (fun i => by simpa only [frame.child_lower, frame.child_sides] using c.contained i) hchild')

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.UniformPhysicalVisitBounds
namespace OAI

section

namespace Erdos3

theorem exists_physical_record_inflation (Ke C Kf : ℕ) :
    ∃ A : ℕ, 1 ≤ A ∧ ∀ x : ℝ, 0 ≤ x →
      x + (x + 2) ^ C ≤ (x + 2) ^ A ∧
      x + (x + 2) ^ Kf + 8 ≤ (x + 2) ^ A ∧
      ∀ q : ℝ, 1 ≤ q → q ≤ (x + 2) ^ Ke → ∀ B : ℕ, B ≤ C →
        (q + B) ^ B ≤ (x + 2) ^ A := by
  let E : Polynomial ℕ := ((Polynomial.X + 2) ^ Ke + Polynomial.C C) ^ C
  let P : Polynomial ℕ := E + Polynomial.X + (Polynomial.X + 2) ^ C +
    Polynomial.X + (Polynomial.X + 2) ^ Kf + 8
  obtain ⟨A, hA, hbudget⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨A, by omega, ?_⟩
  intro x hx
  have hsum : ((x + 2) ^ Ke + C) ^ C + x + (x + 2) ^ C + x + (x + 2) ^ Kf + 8 ≤
      (x + 2) ^ A := by simpa [P, E, Polynomial.eval₂_pow] using hbudget x hx
  have hE : 0 ≤ ((x + 2) ^ Ke + C) ^ C := by positivity
  have hC : 0 ≤ (x + 2) ^ C := by positivity
  have hF : 0 ≤ (x + 2) ^ Kf := by positivity
  refine ⟨by linarith, by linarith, ?_⟩
  intro q hq1 hq B hB
  have hq0 : 0 ≤ q := by linarith
  have hBC : (B : ℝ) ≤ C := by exact_mod_cast hB
  have hbase : q + B ≤ (x + 2) ^ Ke + C := add_le_add hq hBC
  have hlarge : 1 ≤ (x + 2) ^ Ke + C := by have := Nat.cast_nonneg (α := ℝ) C; linarith
  calc
    (q + B) ^ B ≤ ((x + 2) ^ Ke + C) ^ B := pow_le_pow_left₀ (by positivity) hbase B
    _ ≤ ((x + 2) ^ Ke + C) ^ C := pow_le_pow_right₀ hlarge hB
    _ ≤ (x + 2) ^ A := by linarith

theorem inherited_relative_width {W oldWidth newWidth p x D R δ : ℝ}
    (hp : p ≤ x) (hδ : 0 < δ) (hδbound : δ⁻¹ ≤ Real.exp D)
    (hbudget : x + D + 8 ≤ R) (hnew0 : 0 ≤ newWidth)
    (hold : 2 * Real.exp (-p) * W ≤ oldWidth)
    (hnew : δ * oldWidth / 8 ≤ newWidth) :
    2 * Real.exp (-R) * W ≤ newWidth := by
  have hexp : Real.exp p * Real.exp (-p) = 1 := by rw [← Real.exp_add]; simp
  have hold' : 2 * W ≤ Real.exp p * oldWidth := by
    calc
      2 * W = 2 * (Real.exp p * Real.exp (-p)) * W := by rw [hexp]; ring
      _ = Real.exp p * (2 * Real.exp (-p) * W) := by ring
      _ ≤ Real.exp p * oldWidth := mul_le_mul_of_nonneg_left hold (Real.exp_nonneg _)
  have hnew' : oldWidth ≤ 8 * newWidth / δ :=
    (le_div_iff₀ hδ).mpr (by linarith)
  have h8 : (8 : ℝ) ≤ Real.exp 8 := by linarith [Real.add_one_le_exp (8 : ℝ)]
  have hcoeff : 8 * Real.exp p * δ⁻¹ ≤ Real.exp R := by
    calc
      8 * Real.exp p * δ⁻¹ ≤ (Real.exp 8 * Real.exp x) * Real.exp D :=
        mul_le_mul (mul_le_mul h8 (Real.exp_le_exp.mpr hp) (Real.exp_nonneg _) (Real.exp_nonneg _))
          hδbound (inv_nonneg.mpr hδ.le) (by positivity)
      _ = Real.exp (x + D + 8) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp R := Real.exp_le_exp.mpr hbudget
  have htotal : 2 * W ≤ Real.exp R * newWidth := by
    calc
      2 * W ≤ Real.exp p * oldWidth := hold'
      _ ≤ Real.exp p * (8 * newWidth / δ) := mul_le_mul_of_nonneg_left hnew' (Real.exp_nonneg _)
      _ = (8 * Real.exp p * δ⁻¹) * newWidth := by ring
      _ ≤ Real.exp R * newWidth := mul_le_mul_of_nonneg_right hcoeff hnew0
  calc
    2 * Real.exp (-R) * W = Real.exp (-R) * (2 * W) := by ring
    _ ≤ Real.exp (-R) * (Real.exp R * newWidth) := mul_le_mul_of_nonneg_left htotal (Real.exp_nonneg _)
    _ = newWidth := by rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]

end Erdos3

end

section

namespace Erdos3

universe u v

theorem PhysicalEpochFrame.child_comparison_controlled
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J C Kf : ℕ} {gap δ : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (next : PhysicalEpochComparison frame.child m (a * frame.period) J (gap / 4))
    (hc : c.Controlled) (hC : frame.freezePower ≤ C)
    (hperiodBudget : frame.child.incomingBudget + (frame.child.incomingBudget + 2) ^ C ≤ frame.child.recordBudget)
    (hwidthBudget : frame.child.incomingBudget + (frame.child.incomingBudget + 2) ^ Kf + 8 ≤ frame.child.recordBudget)
    (hδ : 0 < δ) (hδbound : δ⁻¹ ≤ Real.exp ((frame.work + 2) ^ Kf))
    (hside : ∀ i, δ * (c.sides i : ℝ) / 8 ≤ (next.sides i : ℝ)) :
    next.Controlled := by
  have hx := frame.child.incoming_nonneg
  have hw : 0 ≤ frame.work := by linarith [base.incoming_nonneg, frame.incoming_le_work]
  have hp : base.recordBudget ≤ frame.child.incomingBudget := by
    linarith [frame.record_le_work, frame.work_le_child]
  have hwx : frame.work + 2 ≤ frame.child.incomingBudget + 2 := by linarith [frame.work_le_child]
  have hpow : (frame.work + 2) ^ frame.freezePower ≤ (frame.child.incomingBudget + 2) ^ C :=
    (pow_le_pow_left₀ (by linarith) hwx _).trans
      (pow_le_pow_right₀ (by linarith) hC)
  have hperiod : (frame.period : ℝ) ≤ Real.exp ((frame.child.incomingBudget + 2) ^ C) :=
    frame.period_le.trans (Real.exp_le_exp.mpr hpow)
  have hδchild : δ⁻¹ ≤ Real.exp ((frame.child.incomingBudget + 2) ^ Kf) :=
    hδbound.trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by linarith) hwx Kf))
  refine ⟨?_, ?_⟩
  · calc
      ((a * frame.period : ℕ) : ℝ) = (a : ℝ) * (frame.period : ℝ) := by norm_cast
      _ ≤ Real.exp frame.child.incomingBudget * Real.exp ((frame.child.incomingBudget + 2) ^ C) :=
        mul_le_mul (hc.1.trans (Real.exp_le_exp.mpr hp)) hperiod (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (frame.child.incomingBudget + (frame.child.incomingBudget + 2) ^ C) := (Real.exp_add _ _).symm
      _ ≤ Real.exp frame.child.recordBudget := Real.exp_le_exp.mpr hperiodBudget
  · intro i
    rw [frame.child_sides]
    exact inherited_relative_width hp hδ hδchild hwidthBudget (Nat.cast_nonneg _) (hc.2 i) (hside i)

theorem PhysicalEpochFrame.extend_records_of_comparison
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap B : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (hc : c.Controlled) (hdiv : ∀ r ∈ frame.state.records, r.modulus ∣ m)
    (hB : B ≤ base.recordBudget)
    (hwide : ∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (c.sides i : ℝ))
    (hevent : ResiduePairDimensionDrop base.model base.weights base.adapted c.test
      (epochRecordIntersection frame.state.records) c.lower c.sides (m * a) c.anchor c.refined
      (fun _ => J) B) :
    ∃ state : PhysicalEpochRecords base,
      (∃ r, state.records = r :: frame.state.records) ∧
      (∀ r ∈ state.records, r.modulus ∣ m * J) ∧ state.dimension < frame.state.dimension := by
  obtain ⟨r, hhistory, hcontrolled, hmoduli, hdrop⟩ :=
    frame.state.history.extend_of_event base.model base.weights base.adapted base.fixedMap c.test
      (fun i => (base.sides i : ℝ)) base.recordBudget B frame.state.records
      frame.state.controlled c.lower c.sides m a J c.selected_pos c.auxiliary_pos c.pending_pos
      hdiv hB hc.1 c.anchor c.refined c.orbit c.compatible hwide
      (fun i => by simpa only [mul_assoc] using hc.2 i) hevent
  exact ⟨⟨r :: frame.state.records, hhistory, hcontrolled⟩, ⟨r, rfl⟩, hmoduli, hdrop⟩

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem exp_neg_le_of_positive_inverse_bound {t F : ℝ} (ht : 0 < t)
    (h : t⁻¹ ≤ Real.exp F) : Real.exp (-F) ≤ t := by
  have hprod : 1 ≤ t * Real.exp F := by
    calc
      1 = t * t⁻¹ := (mul_inv_cancel₀ ht.ne').symm
      _ ≤ t * Real.exp F := mul_le_mul_of_nonneg_left h ht.le
  calc
    Real.exp (-F) = 1 * Real.exp (-F) := (one_mul _).symm
    _ ≤ (t * Real.exp F) * Real.exp (-F) := mul_le_mul_of_nonneg_right hprod (Real.exp_nonneg _)
    _ = t := by rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

theorem physical_visit_numerics {σ : Type*} [Fintype σ]
    (N : σ → ℝ) {M Q U F B ε δ : ℝ}
    (hM : 1 ≤ M) (hMQ : M ≤ Q) (hU : 0 ≤ U) (hF : 0 ≤ F) (hB : B ≤ U)
    (hε : 0 < ε) (hδ : 0 < δ)
    (hεinv : ε⁻¹ ≤ Real.exp F) (hδinv : δ⁻¹ ≤ Real.exp F)
    (hlarge : ∀ i, 16 * ((Fintype.card σ : ℝ) + 1) * Q * Real.exp (U + 2 * F) ≤ N i) :
    (∀ i, 2 * M ≤ N i) ∧
    (∀ i, M * (Real.exp B + 1) ≤ N i) ∧
    (∀ i, 8 ≤ δ * N i) ∧
    (∑ i, Q / N i) ≤ δ * ε / 8 := by
  let k : ℝ := (Fintype.card σ : ℝ) + 1
  have hk : 1 ≤ k := by dsimp [k]; have := Nat.cast_nonneg (α := ℝ) (Fintype.card σ); linarith
  have hQ : 1 ≤ Q := hM.trans hMQ
  have hQ0 : 0 < Q := by linarith
  have hk0 : 0 < k := by linarith
  have hE : 1 ≤ Real.exp U := Real.one_le_exp hU
  have hexpand : Real.exp U ≤ Real.exp (U + 2 * F) := Real.exp_le_exp.mpr (by linarith)
  have hscale : 2 ≤ 16 * k := by linarith
  have hwidth : ∀ i, 2 * Q * Real.exp U ≤ N i := by
    intro i
    calc
      2 * Q * Real.exp U ≤ 16 * k * Q * Real.exp (U + 2 * F) := by gcongr
      _ ≤ N i := hlarge i
  have h16 : ∀ i, 16 * Real.exp (U + 2 * F) ≤ N i := by
    intro i
    calc
      16 * Real.exp (U + 2 * F) ≤ 16 * k * Q * Real.exp (U + 2 * F) := by
        have : 1 ≤ k * Q := one_le_mul_of_one_le_of_one_le hk hQ
        nlinarith [Real.exp_pos (U + 2 * F)]
      _ ≤ N i := hlarge i
  have hδlower := exp_neg_le_of_positive_inverse_bound hδ hδinv
  have hεlower := exp_neg_le_of_positive_inverse_bound hε hεinv
  have hpair : Real.exp (-(2 * F)) ≤ δ * ε := by
    calc
      Real.exp (-(2 * F)) = Real.exp (-F) * Real.exp (-F) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ δ * ε := mul_le_mul hδlower hεlower (Real.exp_nonneg _) hδ.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    calc
      2 * M ≤ 2 * Q * Real.exp U := by nlinarith
      _ ≤ N i := hwidth i
  · intro i
    have : Real.exp B + 1 ≤ 2 * Real.exp U := by linarith [Real.exp_le_exp.mpr hB]
    calc
      M * (Real.exp B + 1) ≤ Q * (2 * Real.exp U) :=
        mul_le_mul hMQ this (by positivity) (by linarith)
      _ = 2 * Q * Real.exp U := by ring
      _ ≤ N i := hwidth i
  · intro i
    have hside : 8 * Real.exp F ≤ N i := by
      calc
        8 * Real.exp F ≤ 16 * Real.exp (U + 2 * F) := by
          have := Real.exp_le_exp.mpr (show F ≤ U + 2 * F by linarith)
          nlinarith [Real.exp_pos F]
        _ ≤ N i := h16 i
    calc
      8 = Real.exp (-F) * (8 * Real.exp F) := by
        rw [show Real.exp (-F) * (8 * Real.exp F) = 8 * (Real.exp (-F) * Real.exp F) by ring,
          ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
      _ ≤ δ * N i := mul_le_mul hδlower hside (by positivity) hδ.le
  · have hterm : ∀ i, Q / N i ≤ (δ * ε) / (16 * k) := by
      intro i
      have hbase : 16 * k * Q * Real.exp (2 * F) ≤ N i := by
        calc
          16 * k * Q * Real.exp (2 * F) ≤ 16 * k * Q * Real.exp (U + 2 * F) := by gcongr; linarith
          _ ≤ N i := hlarge i
      calc
        Q / N i ≤ Q / (16 * k * Q * Real.exp (2 * F)) :=
          div_le_div_of_nonneg_left hQ0.le (by positivity) hbase
        _ = Real.exp (-(2 * F)) / (16 * k) := by
          rw [Real.exp_neg]
          field_simp
        _ ≤ (δ * ε) / (16 * k) := div_le_div_of_nonneg_right hpair (by positivity)
    calc
      (∑ i, Q / N i) ≤ ∑ _i : σ, (δ * ε) / (16 * k) := Finset.sum_le_sum (fun i _ => hterm i)
      _ = (Fintype.card σ : ℝ) * ((δ * ε) / (16 * k)) := by simp
      _ = ((Fintype.card σ : ℝ) / (16 * k)) * (δ * ε) := by ring
      _ ≤ (1 / 8) * (δ * ε) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg hδ.le hε.le)
        apply (div_le_iff₀ (show 0 < 16 * k by positivity)).mpr
        dsimp only [k]
        have := Nat.cast_nonneg (α := ℝ) (Fintype.card σ)
        linarith
      _ = δ * ε / 8 := by ring

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

universe u v

theorem PhysicalEpochFrame.uniform_visit_bounds
    {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap U F B ε δ : ℝ}
    {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
    (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap)
    (hc : c.Controlled) (hrecord : base.recordBudget ≤ U)
    (hperiod : (frame.period : ℝ) ≤ Real.exp U) (hF : 0 ≤ F) (hB : B ≤ U)
    (hε : 0 < ε) (hδ : 0 < δ) (hεinv : ε⁻¹ ≤ Real.exp F) (hδinv : δ⁻¹ ≤ Real.exp F)
    (hsource : ∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * F + 16) ≤ (base.sides i : ℝ)) :
    (∀ i, 2 * ((m * a * J : ℕ) : ℝ) ≤ (c.sides i : ℝ)) ∧
    (∀ i, ((m * a * J : ℕ) : ℝ) * (Real.exp B + 1) ≤ (c.sides i : ℝ)) ∧
    (∀ i, 8 ≤ δ * (c.sides i : ℝ)) ∧
    (∑ i, ((Nat.lcm (m * a) (m * a * frame.period) * J : ℕ) : ℝ) / (c.sides i : ℝ)) ≤ δ * ε / 8 := by
  let k : ℝ := (Fintype.card σ : ℝ) + 1
  let T : ℝ := ((m * J : ℕ) : ℝ)
  let Q : ℝ := ((m * a * frame.period * J : ℕ) : ℝ)
  have hU : 0 ≤ U := base.incoming_nonneg.trans (base.incoming_le_record.trans hrecord)
  have hT : 0 ≤ T := Nat.cast_nonneg _
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have haux : (a : ℝ) ≤ Real.exp U := hc.1.trans (Real.exp_le_exp.mpr hrecord)
  have hQ : Q ≤ T * Real.exp (2 * U) := by
    calc
      Q = T * ((a : ℝ) * (frame.period : ℝ)) := by dsimp [Q, T]; push_cast; ring_nf
      _ ≤ T * (Real.exp U * Real.exp U) :=
        mul_le_mul_of_nonneg_left (mul_le_mul haux hperiod (Nat.cast_nonneg _) (Real.exp_nonneg _)) hT
      _ = T * Real.exp (2 * U) := by rw [← Real.exp_add]; congr 1; ring_nf
  have hkexp : k ≤ Real.exp U := by
    dsimp only [k]
    linarith [base.coordinates_le, base.incoming_le_record, Real.add_one_le_exp U]
  have h16 : (16 : ℝ) ≤ Real.exp 16 := by linarith [Real.add_one_le_exp (16 : ℝ)]
  have hcoeff : 16 * k ≤ Real.exp (U + 16) := by
    calc
      16 * k ≤ Real.exp 16 * Real.exp U := mul_le_mul h16 hkexp hk (Real.exp_nonneg _)
      _ = Real.exp (U + 16) := by rw [← Real.exp_add]; congr 1; ring_nf
  have hsmall : ∀ i, 16 * k * T * Real.exp (4 * U + 2 * F) ≤ (base.sides i : ℝ) := by
    intro i
    calc
      16 * k * T * Real.exp (4 * U + 2 * F) ≤ Real.exp (U + 16) * T * Real.exp (4 * U + 2 * F) := by gcongr
      _ = T * (Real.exp (U + 16) * Real.exp (4 * U + 2 * F)) := by ring_nf
      _ = T * Real.exp (5 * U + 2 * F + 16) := by rw [← Real.exp_add]; congr 1; ring_nf
      _ ≤ (base.sides i : ℝ) := hsource i
  have hlarge : ∀ i, 16 * k * Q * Real.exp (U + 2 * F) ≤ (c.sides i : ℝ) := by
    intro i
    have hexp : Real.exp (2 * U) * Real.exp (U + 2 * F) =
        Real.exp (-U) * Real.exp (4 * U + 2 * F) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring_nf
    calc
      16 * k * Q * Real.exp (U + 2 * F) ≤ 16 * k * (T * Real.exp (2 * U)) * Real.exp (U + 2 * F) := by gcongr
      _ = 16 * k * T * (Real.exp (2 * U) * Real.exp (U + 2 * F)) := by ring_nf
      _ = Real.exp (-U) * (16 * k * T * Real.exp (4 * U + 2 * F)) := by rw [hexp]; ring_nf
      _ ≤ Real.exp (-U) * (base.sides i : ℝ) := mul_le_mul_of_nonneg_left (hsmall i) (Real.exp_nonneg _)
      _ ≤ Real.exp (-base.recordBudget) * (base.sides i : ℝ) := by gcongr
      _ ≤ 2 * Real.exp (-base.recordBudget) * (base.sides i : ℝ) := by
        nlinarith [mul_nonneg (Real.exp_nonneg (-base.recordBudget)) (Nat.cast_nonneg (α := ℝ) (base.sides i))]
      _ ≤ (c.sides i : ℝ) := hc.2 i
  have hM : 1 ≤ ((m * a * J : ℕ) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (Nat.mul_ne_zero c.selected_pos.ne' c.auxiliary_pos.ne') c.pending_pos.ne')
  have hMQ : ((m * a * J : ℕ) : ℝ) ≤ Q := by
    have hp : 1 ≤ frame.period := frame.period_pos
    have h := Nat.mul_le_mul_right J (Nat.mul_le_mul_left (m * a) hp)
    simpa only [Nat.mul_one, Q] using (Nat.cast_le (α := ℝ)).mpr h
  obtain ⟨hwide, hstep, hround, hcount⟩ := physical_visit_numerics (fun i => (c.sides i : ℝ))
    hM hMQ hU hF hB hε hδ hεinv hδinv hlarge
  refine ⟨hwide, hstep, hround, ?_⟩
  have hlcm : Nat.lcm (m * a) (m * a * frame.period) = m * a * frame.period :=
    Nat.lcm_eq_right_iff_dvd.mpr (Nat.dvd_mul_right (m * a) frame.period)
  simpa only [hlcm] using hcount

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Linear.UniformControlledFrameVisit
namespace OAI

section

namespace Erdos3

universe u v

theorem exists_uniform_controlled_frame_visit (C : ℕ) :
    ∃ A Kf : ℕ, 1 ≤ A ∧ 2 ≤ Kf ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap U : ℝ}
      {base : PhysicalEpochSource.{u, v} σ (s + 1) bound}
      (frame : PhysicalEpochFrame base) (c : PhysicalEpochComparison base m a J gap),
    c.Controlled → base.recordBudget ≤ U →
    (base.incomingBudget + 2) ^ A ≤ base.recordBudget →
    (frame.child.incomingBudget + 2) ^ A ≤ frame.child.recordBudget →
    frame.work ≤ U → (frame.period : ℝ) ≤ Real.exp U →
    frame.freezePower ≤ C → frame.eventPower ≤ C →
    frame.modulus ∣ m →
    (∀ i, c.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)]) →
    (m * a * (m * a * frame.period)).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    (∃ state : PhysicalEpochRecords base,
      (∃ r, state.records = r :: frame.state.records) ∧
      (∀ r ∈ state.records, r.modulus ∣ m * J) ∧ state.dimension < frame.state.dimension) ∨
    ∃ next : PhysicalEpochComparison frame.child m (a * frame.period) J (gap / 4),
      next.Controlled ∧
      (∀ i, c.lower i ≤ next.lower i ∧ next.lower i + next.sides i ≤ c.lower i + c.sides i) ∧
      (∀ i, next.anchor i ≡ c.anchor i [ZMOD (m * a : ℕ)]) ∧
      (∀ i, next.refined i ≡ c.refined i [ZMOD (m * a * J : ℕ)]) := by
  obtain ⟨Ke, _, hprecision⟩ := exists_physical_frame_precision
  obtain ⟨Kf, hKf, hprecision⟩ := hprecision C
  obtain ⟨A, hA, hinflation⟩ := exists_physical_record_inflation Ke C Kf
  refine ⟨A, Kf, hA, hKf, ?_⟩
  intro σ _ _ s bound m a J gap U base frame c hc hrecord hbase hchild hwork hperiod hfreeze hevent hmod hanchor hcop hsource
  have hU : 0 ≤ U := base.incoming_nonneg.trans (base.incoming_le_record.trans hrecord)
  have hwork0 : 0 ≤ frame.work := by linarith [base.incoming_nonneg, frame.incoming_le_work]
  obtain ⟨rho, q, ε, δ, hpq, hfreq, hq, hrho, hrhop, hε, hεhalf, hδ, hδone,
    hεinv, hδinv, hprojection, hfreezing⟩ := hprecision frame c hfreeze
  have hq1 : 1 ≤ q := by linarith [base.incoming_nonneg]
  have hB : (q + frame.eventPower) ^ frame.eventPower ≤ base.recordBudget :=
    ((hinflation base.incomingBudget base.incoming_nonneg).2.2 q hq1 hq frame.eventPower hevent).trans hbase
  have hF : (frame.work + 2) ^ Kf ≤ (U + 2) ^ Kf :=
    pow_le_pow_left₀ (by linarith) (by linarith) Kf
  obtain ⟨hwide, hstep, hround, hcount⟩ := frame.uniform_visit_bounds c hc hrecord hperiod
    (show 0 ≤ (U + 2) ^ Kf by positivity) (hB.trans hrecord) hε hδ
    (hεinv.trans (Real.exp_le_exp.mpr hF)) (hδinv.trans (Real.exp_le_exp.mpr hF)) hsource
  rcases frame.visit c (hmod.trans (Nat.dvd_mul_right m a)) hanchor q rho ε δ
      hpq hfreq hrho hrhop hcop hstep hδ hδone hεhalf hprojection hfreezing hround hcount with he | hn
  · exact Or.inl (frame.extend_records_of_comparison c hc
      (fun r hr => (frame.record_moduli r hr).trans hmod) hB hwide he)
  · obtain ⟨next, hcontained, hside, hnextAnchor, hnextRefined⟩ := hn
    have hc' := frame.child_comparison_controlled c next hc hfreeze
      ((hinflation frame.child.incomingBudget frame.child.incoming_nonneg).1.trans hchild)
      ((hinflation frame.child.incomingBudget frame.child.incoming_nonneg).2.1.trans hchild)
      hδ hδinv (fun i => (hside i).1)
    exact Or.inr ⟨next, hc', hcontained, hnextAnchor, hnextRefined⟩

end Erdos3

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Estimates.PhysicalStabilityParameters
namespace OAI

section

namespace Erdos3

universe u v

open PhysicalEpochStack

theorem exists_physical_stack_record_descent_s2_oai (C : ℕ) :
    ∃ A Kf : ℕ, 1 ≤ A ∧ 2 ≤ Kf ∧
    ∀ {σ : Type u} [Fintype σ] [DecidableEq σ] {s bound m a J : ℕ} {gap U : ℝ}
      (selected : σ → ℤ) {base : PhysicalEpochSource.{u, v} σ s bound}
      (stack : PhysicalEpochStack base) (c : PhysicalEpochComparison base m a J gap),
    BudgetedAt A U C stack → AlignedAt m selected stack → c.Controlled →
    (∀ i, c.anchor i ≡ selected i [ZMOD (m : ℤ)]) →
    (m * a * stack.periods.prod).Coprime J →
    (∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) ≤ (base.sides i : ℝ)) →
    RecordEvent m J stack := by
  obtain ⟨A, Kf, hA, hKf, hvisit⟩ := exists_uniform_controlled_frame_visit C
  refine ⟨A, Kf, hA, hKf, ?_⟩
  intro σ _ _ s bound m a J gap U selected base stack
  revert a gap
  induction stack with
  | zero base =>
    intro a gap c hbudget halign hc hanchor hcop hsource
    exact False.elim c.impossible_at_zero
  | @succ s base frame tail ih =>
    intro a gap c hbudget halign hc hanchor hcop hsource
    obtain ⟨hrecord, hinflate, hwork, hperiod, hfreeze, hevent, htail⟩ := hbudget
    obtain ⟨hmod, halign, htailAlign⟩ := halign
    have hchild : (frame.child.incomingBudget + 2) ^ A ≤ frame.child.recordBudget := by
      cases tail with
      | zero => exact htail.2
      | succ => exact htail.2.1
    have hframeAnchor : ∀ i, c.anchor i ≡ frame.anchor i [ZMOD (frame.modulus : ℤ)] := by
      intro i
      exact (Int.ModEq.of_dvd (by exact_mod_cast hmod) (hanchor i)).trans (halign i)
    have hleft : (m * a).Coprime J := Nat.Coprime.of_dvd_left (Nat.dvd_mul_right _ _) hcop
    have hperiodDiv : m * a * frame.period ∣ m * a * (PhysicalEpochStack.succ frame tail).periods.prod := by
      simpa only [periods, List.prod_cons, Nat.mul_assoc] using Nat.dvd_mul_right (m * a * frame.period) tail.periods.prod
    have hright : (m * a * frame.period).Coprime J := Nat.Coprime.of_dvd_left hperiodDiv hcop
    have hlocal : (m * a * (m * a * frame.period)).Coprime J := (hleft.symm.mul_right hright.symm).symm
    rcases hvisit frame c hc hrecord hinflate hchild hwork hperiod hfreeze hevent
        hmod hframeAnchor hlocal hsource with hrecordEvent | hnext
    · obtain ⟨state, hr, hm, hd⟩ := hrecordEvent
      exact .head frame tail state hr hm hd
    · obtain ⟨next, hnextControl, _, hnextAnchor, _⟩ := hnext
      have hanchor' : ∀ i, next.anchor i ≡ selected i [ZMOD (m : ℤ)] := by
        intro i
        exact (Int.ModEq.of_dvd (by exact_mod_cast Nat.dvd_mul_right m a) (hnextAnchor i)).trans (hanchor i)
      have hcop' : (m * (a * frame.period) * tail.periods.prod).Coprime J := by
        simpa only [periods, List.prod_cons, Nat.mul_assoc] using hcop
      have hsource' : ∀ i, ((m * J : ℕ) : ℝ) * Real.exp (5 * U + 2 * (U + 2) ^ Kf + 16) ≤
          (frame.child.sides i : ℝ) := by
        simpa only [frame.child_sides] using hsource
      exact .tail frame (ih next htail htailAlign hnextControl hanchor' hcop' hsource')

end Erdos3

end

end OAI
end

theorem solution.{u, v} : type_of% @OAI.Erdos3.exists_physical_stack_record_descent_s2_oai.{u, v} := @OAI.Erdos3.exists_physical_stack_record_descent_s2_oai.{u, v}
