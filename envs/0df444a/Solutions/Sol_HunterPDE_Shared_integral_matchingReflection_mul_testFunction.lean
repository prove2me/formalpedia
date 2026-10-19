-- Prove2me | solution 1 for HunterPDE.Shared.integral_matchingReflection_mul_testFunction
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-16T13:29:15.375538+00:00
-- url     : https://prove2.me/submissions/4435ddc2-01a6-4479-a3e2-763eddf0d074

import Theorems.Thm_HunterPDE_Shared_iteratedPartial_sum_coordinate_pullback
import Theorems.Thm_HunterPDE_Shared_HasWeakDeriv_integral_mul_normalJetVanishing
import Theorems.Thm_MeasureTheory_integral_finite_halfSpace_reflection
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

open MeasureTheory HunterPDE.Shared
open scoped ENNReal ContDiff
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {n N : ℕ} (i : Fin n) (α : Fin n → ℕ) (p : ℝ≥0∞) (hp : 1 ≤ p)
    (b c : Fin N → ℝ) (hb : ∀ j, 0 < b j)
    (hc : ∀ r : ℕ, r < α i → ∑ j : Fin N, c j * (-b j) ^ r = 1)
    (f g : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf : MemLp f p (volume.restrict {x | 0 < x i}))
    (hg : MemLp g p (volume.restrict {x | 0 < x i}))
    (hd : HunterPDE.Shared.HasWeakDeriv {x | 0 < x i} α f g)
    (φ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hφ : HunterPDE.Shared.IsTestFunction Set.univ φ) :
    (∫ x, (if 0 < x i then g x else
      ∑ j : Fin N, (c j * (-b j) ^ (α i)) *
        g (WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)))) * φ x) =
    (-1 : ℝ) ^ (∑ l, α l) *
      ∫ x, (if 0 < x i then f x else
        ∑ j : Fin N, c j *
          f (WithLp.toLp 2 (Function.update (fun l => x l) i (-b j * x i)))) *
        HunterPDE.Shared.multiDeriv φ α x := by
  classical
  let E := EuclideanSpace ℝ (Fin n)
  let a : ℕ := α i
  let q : Fin N → ℝ := fun j => -b j
  have hq (j : Fin N) : q j ≠ 0 := neg_ne_zero.mpr (ne_of_gt (hb j))
  let e (j : Fin N) : E ≃L[ℝ] E :=
    ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).trans
      ((LinearEquiv.piCongrRight fun k : Fin n =>
        LinearEquiv.smulOfNeZero ℝ ℝ (if k = i then (q j)⁻¹ else 1)
          (by split_ifs <;> simp [hq j])).trans
        (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm)).toContinuousLinearEquiv
  have he (j : Fin N) (x : E) (k : Fin n) :
      e j x k = (if k = i then (q j)⁻¹ else 1) * x k := by
    by_cases hk : k = i
    all_goals
      simp [e, LinearEquiv.piCongrRight_apply, LinearEquiv.smulOfNeZero,
        LinearEquiv.smulOfUnit, hk]
      first | exact Or.inl rfl | rfl
  have heform (j : Fin N) (x : E) : e j x =
      WithLp.toLp 2 (Function.update (fun k => x k) i (-(b j)⁻¹ * x i)) := by
    ext k
    by_cases hk : k = i <;> simp [he, hk, q]
  have hebasis (j : Fin N) (k : Fin n) :
      e j (EuclideanSpace.single k 1) =
        (if k = i then (q j)⁻¹ else 1) • EuclideanSpace.single k 1 := by
    ext l
    rw [he]
    change (if l = i then (q j)⁻¹ else 1) *
        (EuclideanSpace.single k (1 : ℝ)) l =
      (if k = i then (q j)⁻¹ else 1) * (EuclideanSpace.single k (1 : ℝ)) l
    by_cases hl : l = k
    · subst l; rfl
    · have hz : (EuclideanSpace.single k (1 : ℝ)) l = 0 := by simp [hl]
      rw [hz, mul_zero, mul_zero]
  let w : Fin N → ℝ := fun j => c j * q j ^ a / b j
  let A : Option (Fin N) → ℝ := fun j => j.elim 1 w
  let T : Option (Fin N) → ℝ := fun j => j.elim 1 (fun j => (q j)⁻¹)
  let L : Option (Fin N) → E →L[ℝ] E :=
    fun j => j.elim (ContinuousLinearMap.id ℝ E) (fun j => (e j).toContinuousLinearMap)
  let ψ : E → ℝ := fun x => ∑ j : Option (Fin N), A j * φ (L j x)
  have hψform (x : E) : ψ x = φ x + ∑ j : Fin N, w j * φ (e j x) := by
    simp [ψ, A, L, Fintype.sum_option]
  have hL (j : Option (Fin N)) (k : Fin n) :
      L j (EuclideanSpace.single k 1) =
        (if k = i then T j else 1) • EuclideanSpace.single k 1 := by
    cases j with
    | none => simp [L, T]
    | some j => exact hebasis j k
  have hword (l : List (Fin n)) (x : E) :
      iteratedPartial ψ l x = iteratedPartial φ l x +
        ∑ j : Fin N, (w j * ((q j)⁻¹) ^ l.count i) * iteratedPartial φ l (e j x) := by
    have hh := congrFun (HunterPDE.Shared.iteratedPartial_sum_coordinate_pullback
      i A T L hL (fun _ => φ) (fun _ => hφ.1) l) x
    simpa [ψ, A, T, L, E, Fintype.sum_option] using hh
  have hψ : IsTestFunction Set.univ ψ := by
    refine ⟨?_, ?_, Set.subset_univ _⟩
    · exact ContDiff.sum (fun j _ => contDiff_const.mul (hφ.1.comp (L j).contDiff))
    · have hh : HasCompactSupport (∑ j : Option (Fin N), fun x => A j * φ (L j x)) := by
        apply HasCompactSupport.finset_sum
        intro j _
        cases j with
        | none => simpa [A, L, E] using hφ.2.1
        | some j => exact (hφ.2.1.comp_homeomorph (e j).toHomeomorph).mul_left
      have hfun : (∑ j : Option (Fin N), fun x => A j * φ (L j x)) = ψ := by
        funext x
        simp [ψ]
      exact hfun ▸ hh
  have hcoeff (j : Fin N) : w j * ((q j)⁻¹) ^ a = c j / b j := by
    simp only [w, inv_pow]
    field_simp [hq j]
  have hjetcoeff (j : Fin N) (r : ℕ) (hr : r < a) :
      w j * ((q j)⁻¹) ^ r = -c j * q j ^ (a - r - 1) := by
    have ha : a = (a - r - 1) + r + 1 := by omega
    have hpow : q j ^ a = q j ^ (a-r-1) * q j ^ r * q j := by
      conv_lhs => rw [ha, pow_add, pow_add]
      simp
    dsimp [w]
    rw [hpow, inv_pow]
    field_simp [hq j, ne_of_gt (hb j)]
    dsimp [q]
    ring
  have hbψ : ∀ r : ℕ, r < α i → ∀ x : E, x i = 0 →
      iteratedPartial ψ (List.replicate r i) x = 0 := by
    intro r hr x hx
    have hfix (j : Fin N) : e j x = x := by
      ext k
      by_cases hk : k = i <;> simp [he, hk, hx]
    rw [hword]
    simp only [List.count_replicate_self, hfix]
    simp_rw [hjetcoeff _ r hr]
    have hm := hc (a-r-1) (by change r < a at hr; change a-r-1 < a; omega)
    change (∑ j : Fin N, c j * q j ^ (a-r-1)) = 1 at hm
    simp only [neg_mul]
    rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hm]
    ring
  have hcount : (multiIndexList α).count i = α i := by
    rw [multiIndexList, List.count_flatMap]
    simp only [Function.comp_def, List.count_replicate, beq_iff_eq]
    rw [← List.ofFn_eq_map, List.sum_ofFn]
    simp
  have hdψ (x : E) : multiDeriv ψ α x = multiDeriv φ α x +
      ∑ j : Fin N, (c j / b j) * multiDeriv φ α (e j x) := by
    simpa only [multiDeriv, hcount, show α i = a from rfl, hcoeff] using
      hword (multiIndexList α) x
  have hsmooth : ContDiff ℝ ∞ (multiDeriv φ α) := by
    change ContDiff ℝ ∞ (iteratedPartial φ (multiIndexList α))
    generalize multiIndexList α = l
    induction l with
    | nil => exact hφ.1
    | cons k l ih =>
      exact (ih.contDiff_fderiv_apply (m := ∞) (by simp)).comp
        (contDiff_id.prodMk contDiff_const)
  have hcompact : HasCompactSupport (multiDeriv φ α) := by
    change HasCompactSupport (iteratedPartial φ (multiIndexList α))
    generalize multiIndexList α = l
    induction l with
    | nil => exact hφ.2.1
    | cons k l ih => exact HasCompactSupport.fderiv_apply ℝ ih (EuclideanSpace.single k 1)
  have hleft := MeasureTheory.integral_finite_halfSpace_reflection i b
    (fun j => c j * (-b j) ^ (α i)) hb g φ (hg.locallyIntegrable hp) hφ.1.continuous hφ.2.1
  have hright := MeasureTheory.integral_finite_halfSpace_reflection i b c hb f
    (multiDeriv φ α) (hf.locallyIntegrable hp) hsmooth.continuous hcompact
  have hboundary := HunterPDE.Shared.HasWeakDeriv.integral_mul_normalJetVanishing
    i α f g ψ (hf.locallyIntegrable hp) (hg.locallyIntegrable hp) hd hψ hbψ
  rw [hleft]
  calc
    _ = ∫ x in {x : E | 0 < x i}, g x * ψ x := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [hψform, heform, w, q, a]
    _ = _ := hboundary
    _ = _ := by
      rw [hright]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [hdψ, heform]
