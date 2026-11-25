-- Prove2me | solution 1 for GroundTheory.Global.exists_rat_intertwiner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:08:48.808298+00:00
-- url     : https://prove2.me/submissions/e17eca2b-0975-42cb-a89e-ef272b9bd69d

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_RationalForm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open Matrix
namespace GroundTheory.Global
theorem _root_.solution {ι J : Type*} [Fintype ι] [DecidableEq ι]
    (A A' : J → Matrix ι ι ℚ) (P : Matrix ι ι ℝ) (hP : P.det ≠ 0)
    (h : ∀ j, P * (A j).map (Rat.cast : ℚ → ℝ) = (A' j).map (Rat.cast : ℚ → ℝ) * P) :
    ∃ Q : Matrix ι ι ℚ, Q.det ≠ 0 ∧ ∀ j, Q * A j = A' j * Q := by

  obtain ⟨V, hV⟩ : ∃ V : Submodule ℚ ℝ,
      V = Submodule.span ℚ (Set.range fun p : ι × ι => P p.1 p.2) := ⟨_, rfl⟩
  have : Module.Finite ℚ V := hV ▸ Module.Finite.span_of_finite ℚ (Set.finite_range _)
  obtain ⟨κ, _, ⟨c⟩⟩ : ∃ (κ : Type) (_ : Fintype κ), Nonempty (Module.Basis κ ℚ V) :=
    ⟨_, inferInstance, ⟨Module.Free.chooseBasis ℚ V⟩⟩
  have hmem : ∀ a b, P a b ∈ V := fun a b => hV ▸ Submodule.subset_span ⟨(a, b), rfl⟩

  let Bm : κ → Matrix ι ι ℚ := fun k a b => c.repr ⟨P a b, hmem a b⟩ k
  have hcast : ∀ (q : ℚ) (r : ℝ), q • r = (q : ℝ) * r := fun q r => by
    rw [Algebra.smul_def, eq_ratCast]
  have hP_eq : P = ∑ k, (c k : ℝ) • (Bm k).map (Rat.cast : ℚ → ℝ) := by
    ext a b
    have h1 := congrArg (Subtype.val : V → ℝ) (c.sum_repr ⟨P a b, hmem a b⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul, hcast] at h1
    rw [Matrix.sum_apply]
    simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    rw [← h1]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _
  have hli : LinearIndependent ℚ (fun k => (c k : ℝ)) :=
    c.linearIndependent.map' V.subtype (Submodule.ker_subtype V)

  have hB : ∀ k j, Bm k * A j = A' j * Bm k := by
    intro k j
    have hsum : ∑ k, (c k : ℝ) • (Bm k * A j - A' j * Bm k).map (Rat.cast : ℚ → ℝ) = 0 := by
      have hmap : ∀ X Y : Matrix ι ι ℚ, (X * Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) * Y.map (Rat.cast : ℚ → ℝ) := fun X Y =>
        Matrix.map_mul (f := Rat.castHom ℝ)
      have hsub : ∀ X Y : Matrix ι ι ℚ, (X - Y).map (Rat.cast : ℚ → ℝ) =
          X.map (Rat.cast : ℚ → ℝ) - Y.map (Rat.cast : ℚ → ℝ) := fun X Y => by
        ext; simp
      have e1 : ∑ k, (c k : ℝ) • ((Bm k).map (Rat.cast : ℚ → ℝ) * (A j).map (Rat.cast : ℚ → ℝ)) =
          P * (A j).map (Rat.cast : ℚ → ℝ) := by
        rw [hP_eq, Finset.sum_mul]
        simp only [Matrix.smul_mul]
      have e2 : ∑ k, (c k : ℝ) • ((A' j).map (Rat.cast : ℚ → ℝ) * (Bm k).map (Rat.cast : ℚ → ℝ)) =
          (A' j).map (Rat.cast : ℚ → ℝ) * P := by
        rw [hP_eq, Finset.mul_sum]
        simp only [Matrix.mul_smul]
      simp only [hsub, hmap, smul_sub, Finset.sum_sub_distrib, e1, e2, h j, sub_self]
    ext a b
    have hab := congrFun (congrFun hsum a) b
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
      Matrix.zero_apply] at hab
    have := Fintype.linearIndependent_iff.1 hli (fun k => (Bm k * A j - A' j * Bm k) a b)
      (by simpa only [hcast, mul_comm] using hab) k
    rwa [Matrix.sub_apply, sub_eq_zero] at this

  clear_value Bm
  obtain ⟨Mx, hMx⟩ : ∃ Mx : Matrix ι ι (MvPolynomial κ ℚ),
      Mx = Matrix.of fun a b => ∑ k, MvPolynomial.X k * MvPolynomial.C (Bm k a b) := ⟨_, rfl⟩
  have hev : ∀ (t : κ → ℝ),
      (MvPolynomial.aeval t : MvPolynomial κ ℚ →ₐ[ℚ] ℝ).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, t k * algebraMap ℚ ℝ (Bm k a b) := by
    intro t
    ext a b
    rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [hMx, Matrix.of_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C]
  have hPof : P = Matrix.of fun a b => ∑ k, (c k : ℝ) * algebraMap ℚ ℝ (Bm k a b) := by
    refine hP_eq.trans ?_
    ext a b
    rw [Matrix.sum_apply, Matrix.of_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, eq_ratCast]
  have hF : Mx.det ≠ 0 := by
    intro h0
    apply hP
    rw [hPof, ← hev, ← AlgHom.map_det, h0]
    exact map_zero _
  obtain ⟨q, hq⟩ : ∃ q : κ → ℚ, MvPolynomial.eval q Mx.det ≠ 0 := by
    by_contra! hall
    exact hF (MvPolynomial.funext fun x => by rw [hall x, map_zero])
  refine ⟨∑ k, q k • Bm k, ?_, fun j => ?_⟩
  · have hQ : ∑ k, q k • Bm k = Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      rw [Matrix.sum_apply, Matrix.of_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Matrix.smul_apply, smul_eq_mul, Algebra.algebraMap_self, RingHom.id_apply]
    have hevq : (MvPolynomial.eval q).mapMatrix Mx =
        Matrix.of fun a b => ∑ k, q k * algebraMap ℚ ℚ (Bm k a b) := by
      ext a b
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, hMx, Matrix.of_apply, Matrix.of_apply,
        map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_C, Algebra.algebraMap_self,
        RingHom.id_apply]
    have := RingHom.map_det (MvPolynomial.eval q) Mx
    rw [hevq] at this
    rw [hQ, ← this]
    exact hq
  · rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.smul_mul, Matrix.mul_smul, hB]
end GroundTheory.Global
