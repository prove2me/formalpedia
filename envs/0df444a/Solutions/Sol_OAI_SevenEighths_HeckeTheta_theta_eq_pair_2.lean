-- Prove2me | solution 2 for OAI.SevenEighths.HeckeTheta.theta_eq_pair
-- status  : ACCEPTED   (prove)
-- author  : @Secousses
-- created : 2026-11-05T23:06:38.922208+00:00
-- url     : https://prove2.me/submissions/1bf1190d-d13a-4ebc-b47d-cc15272b8c62

import Definitions.Def_OAI_NumberTheory_DirichletL_EisensteinTheta
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.NumberTheory.LSeries.MellinEqDirichlet
import Definitions.Def_OAI_NumberTheory_DirichletL_Hecke_Theta
set_option autoImplicit false
open OAI
noncomputable section
open Filter Asymptotics Set MeasureTheory
open scoped Topology BigOperators
open OAI.SevenEighths OAI.SevenEighths.HeckeTheta
open EisensteinTheta

theorem OA1Aux.hasSum_fibres {ι κ α : Type*} [Fintype ι] [DecidableEq ι] [AddCommMonoid α]
    [TopologicalSpace α] [ContinuousAdd α] {f : ι → κ → α} {a : ι → α}
    (h : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun x : ι × κ => f x.1 x.2) (∑ i, a i) := by
  have hdecomp : (fun x : ι × κ => f x.1 x.2) =
      fun x : ι × κ => ∑ i : ι, (if x.1 = i then f i x.2 else 0) := by
    funext x
    simp
  rw [hdecomp]
  refine hasSum_sum (fun i _ => ?_)
  have hinj : Function.Injective (fun q : κ => (i, q)) := fun _ _ hq => (Prod.mk.inj hq).2
  rw [← hinj.hasSum_iff]
  · have hc : ((fun x : ι × κ => if x.1 = i then f i x.2 else 0) ∘ fun q => (i, q)) = f i := by
      funext q
      simp
    rw [hc]
    exact h i
  · intro x hx
    have : x.1 ≠ i := by
      intro h1
      exact hx ⟨x.2, Prod.ext h1.symm rfl⟩
    simp [this]

theorem OA1Aux.hasSum_coset (a b L t : ℝ) (hL : 0 < L) (ht : 0 < t) :
    HasSum (fun m : ℤ × ℤ => Real.exp (-Real.pi * normForm (a + L * m.1) (b + L * m.2) * t))
      (∑ e : Fin 2, HurwitzZeta.evenKernel ((xShift a b L e : ℝ) : UnitAddCircle) (L ^ 2 * t) *
        HurwitzZeta.evenKernel ((yShift b L e : ℝ) : UnitAddCircle) (3 * L ^ 2 * t)) := by
  have hfib : ∀ e : Fin 2, HasSum (fun q : ℤ × ℤ =>
      Real.exp (-Real.pi * (q.1 + xShift a b L e) ^ 2 * (L ^ 2 * t)) *
        Real.exp (-Real.pi * (q.2 + yShift b L e) ^ 2 * (3 * L ^ 2 * t)))
      (HurwitzZeta.evenKernel ((xShift a b L e : ℝ) : UnitAddCircle) (L ^ 2 * t) *
        HurwitzZeta.evenKernel ((yShift b L e : ℝ) : UnitAddCircle) (3 * L ^ 2 * t)) := by
    intro e
    have h1 := HurwitzZeta.hasSum_int_evenKernel (xShift a b L e) (by positivity : 0 < L ^ 2 * t)
    have h2 := HurwitzZeta.hasSum_int_evenKernel (yShift b L e) (by positivity : 0 < 3 * L ^ 2 * t)
    exact h1.mul h2 (Summable.mul_of_nonneg h1.summable h2.summable
      (fun _ => (Real.exp_pos _).le) (fun _ => (Real.exp_pos _).le))
  have hG := OA1Aux.hasSum_fibres (f := fun (e : Fin 2) (q : ℤ × ℤ) =>
      Real.exp (-Real.pi * (q.1 + xShift a b L e) ^ 2 * (L ^ 2 * t)) *
        Real.exp (-Real.pi * (q.2 + yShift b L e) ^ 2 * (3 * L ^ 2 * t))) hfib
  rw [← parityEquiv.symm.hasSum_iff]
  convert hG using 1
  funext x
  obtain ⟨e, p, q⟩ := x
  simp only [Function.comp, parityEquiv, shearEquiv, Equiv.trans_apply, Equiv.symm_trans_apply,
    Equiv.coe_fn_symm_mk, Equiv.prodCongr_symm, Equiv.prodCongr_apply, Equiv.symm_symm,
    Prod.map, Equiv.refl_symm, Equiv.refl_apply, Int.divModEquiv_symm_apply]
  rw [← Real.exp_add]
  congr 1
  unfold normForm xShift yShift
  push_cast
  field_simp
  ring


theorem OA1Aux.pair_f {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) (t : ℝ) :
    (pair w).f t = ∑ r : Fin N × Fin N, w r *
      ((∑ e : Fin 2, HurwitzZeta.evenKernel
          ((xShift ((r.1 : ℕ) : ℝ) ((r.2 : ℕ) : ℝ) (N : ℝ) e : ℝ) : UnitAddCircle)
            ((N : ℝ) ^ 2 * t) *
        HurwitzZeta.evenKernel ((yShift ((r.2 : ℕ) : ℝ) (N : ℝ) e : ℝ) : UnitAddCircle)
          (3 * (N : ℝ) ^ 2 * t) : ℝ) : ℂ) := by
  simp only [pair, finitePair, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  dsimp only
  rw [← Finset.mul_sum]
  congr 1
  push_cast
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rfl

theorem OA1Aux.hasSum_theta {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ) {t : ℝ} (ht : 0 < t) :
    HasSum (fun n : ℤ × ℤ => periodicCoeff w n * (Real.exp (-Real.pi * normForm n.1 n.2 * t) : ℂ))
      ((pair w).f t) := by
  have hL : (0 : ℝ) < N := Nat.cast_pos.mpr (NeZero.pos N)
  have hfib : ∀ r : Fin N × Fin N, HasSum (fun m : ℤ × ℤ => w r *
      (Real.exp (-Real.pi * normForm (((r.1 : ℕ) : ℝ) + (N : ℝ) * m.1)
        (((r.2 : ℕ) : ℝ) + (N : ℝ) * m.2) * t) : ℂ))
      (w r * ((∑ e : Fin 2, HurwitzZeta.evenKernel
          ((xShift ((r.1 : ℕ) : ℝ) ((r.2 : ℕ) : ℝ) (N : ℝ) e : ℝ) : UnitAddCircle)
            ((N : ℝ) ^ 2 * t) *
        HurwitzZeta.evenKernel ((yShift ((r.2 : ℕ) : ℝ) (N : ℝ) e : ℝ) : UnitAddCircle)
          (3 * (N : ℝ) ^ 2 * t) : ℝ) : ℂ)) := fun r =>
    (Complex.hasSum_ofReal.mpr
      (OA1Aux.hasSum_coset ((r.1 : ℕ) : ℝ) ((r.2 : ℕ) : ℝ) (N : ℝ) t hL ht)).mul_left (w r)
  have hF := OA1Aux.hasSum_fibres hfib
  rw [OA1Aux.pair_f]
  rw [← (residueEquiv N).symm.hasSum_iff]
  convert hF using 1
  funext x
  obtain ⟨r, m⟩ := x
  have hp : periodicCoeff w ((residueEquiv N).symm (r, m)) = w r := by
    simp [periodicCoeff]
  have e1 : ((((residueEquiv N).symm (r, m)).1 : ℤ) : ℝ) = ((r.1 : ℕ) : ℝ) + (N : ℝ) * m.1 := by
    simp [residueEquiv, regroup, Int.divModEquiv]
    ring
  have e2 : ((((residueEquiv N).symm (r, m)).2 : ℤ) : ℝ) = ((r.2 : ℕ) : ℝ) + (N : ℝ) * m.2 := by
    simp [residueEquiv, regroup, Int.divModEquiv]
    ring
  simp only [Function.comp_apply, hp, e1, e2]

theorem solution {N : ℕ} [NeZero N] (w : Fin N × Fin N → ℂ)
    {t : ℝ} (ht : 0 < t) : theta w t = (pair w).f t := by
  unfold theta
  exact (OA1Aux.hasSum_theta w ht).tsum_eq
