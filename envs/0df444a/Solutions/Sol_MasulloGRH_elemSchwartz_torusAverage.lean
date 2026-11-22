-- Prove2me | solution 1 for MasulloGRH.elemSchwartz_torusAverage
-- status  : ACCEPTED   (prove)
-- author  : @sflicht
-- created : 2026-11-21T17:09:08.922768+00:00
-- url     : https://prove2.me/submissions/62b438bb-57e0-491b-8cd8-eee6086882f4

import Theorems.Thm_MasulloGRH_contDiff_integral_of_bounded_iteratedFDeriv
import Theorems.Thm_MasulloGRH_isRapidDecay_elemSchwartz_toFun
import Theorems.Thm_MasulloGRH_elemSchwartz_continuous_of_seminorm_bound

set_option autoImplicit false

open MeasureTheory Topology Filter

namespace MasulloGRHAvgAux

open MasulloGRH

variable {m n r s : ℕ} {d : Fin s → ℕ} (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν]

lemma top_le (k : ℕ) : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
  exact_mod_cast le_top

noncomputable def avgFun (g : ElemGroup m n r s d → ℂ) : ElemGroup m n r s d → ℂ :=
  fun e => ∫ v, g (e.1, e.2.1 + (fun j => ((v j : ℝ) : UnitAddCircle)), e.2.2) ∂ν

def sh (v : Fin n → ℝ) : (Fin m → ℝ) × (Fin n → ℝ) := (0, v)

omit [IsFiniteMeasure ν] in
lemma fst_add_sh (xt : (Fin m → ℝ) × (Fin n → ℝ)) (v : Fin n → ℝ) : (xt + sh v).1 = xt.1 := by
  simp [sh]

lemma elemLift_avgFun (g : ElemGroup m n r s d → ℂ) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) :
    elemLift (avgFun ν g) a b = fun xt => ∫ v, elemLift g a b (xt + sh (m := m) v) ∂ν := by
  funext xt
  simp only [elemLift, avgFun, sh, Prod.fst_add, Prod.snd_add, add_zero, Pi.add_apply,
    AddCircle.coe_add]
  rfl

variable {ν}

/-- the main analytic facts for a rapid decay function -/
lemma key {g : ElemGroup m n r s d → ℂ} (hg : IsRapidDecay g) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (elemLift (avgFun ν g) a b) ∧
      ∀ (k : ℕ) xt, iteratedFDeriv ℝ k (elemLift (avgFun ν g) a b) xt =
        ∫ v, iteratedFDeriv ℝ k (elemLift g a b) (xt + sh (m := m) v) ∂ν := by
  rw [elemLift_avgFun]
  have hF : ∀ v : Fin n → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun xt => elemLift g a b (xt + sh (m := m) v)) := fun v =>
    (hg.1 a b).comp (contDiff_id.add contDiff_const)
  have hD : ∀ (k : ℕ) (v : Fin n → ℝ) xt,
      iteratedFDeriv ℝ k (fun xt => elemLift g a b (xt + sh (m := m) v)) xt =
        iteratedFDeriv ℝ k (elemLift g a b) (xt + sh v) := fun k v xt =>
    iteratedFDeriv_comp_add_right k _ xt
  have h := contDiff_integral_of_bounded_iteratedFDeriv ν
    (fun v xt => elemLift g a b (xt + sh (m := m) v)) hF
    (fun k y => by
      simp only [hD]
      exact (((hg.1 a b).continuous_iteratedFDeriv (top_le k)).comp
        (continuous_const.add (continuous_const.prodMk continuous_id))).aestronglyMeasurable)
    (fun k => by
      obtain ⟨C, hC⟩ := hg.2 0 0 k
      exact ⟨C, fun v y => by
        rw [hD]
        simpa using hC a b (y + sh v)⟩)
  exact ⟨h.1, fun k xt => by rw [h.2 k xt]; simp only [hD]⟩

lemma bound {g : ElemGroup m n r s d → ℂ} (hg : IsRapidDecay g) (a : Fin r → ℤ)
    (b : (i : Fin s) → ZMod (d i)) (k : ℕ) (xt : (Fin m → ℝ) × (Fin n → ℝ)) (w M : ℝ)
    (hw : 0 ≤ w)
    (hM : ∀ v : Fin n → ℝ, w * ‖iteratedFDeriv ℝ k (elemLift g a b) (xt + sh v)‖ ≤ M) :
    w * ‖iteratedFDeriv ℝ k (elemLift (avgFun ν g) a b) xt‖ ≤ ν.real Set.univ * M := by
  have hM0 : 0 ≤ M := (mul_nonneg hw (norm_nonneg _)).trans (hM 0)
  rw [(key hg a b).2 k xt]
  rcases hw.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; exact mul_nonneg measureReal_nonneg hM0
  · have hb : ∀ v : Fin n → ℝ, ‖iteratedFDeriv ℝ k (elemLift g a b) (xt + sh v)‖ ≤ M / w :=
      fun v => by rw [le_div_iff₀ hpos, mul_comm]; exact hM v
    have := norm_integral_le_of_norm_le_const (μ := ν) (Eventually.of_forall hb)
    calc w * ‖∫ v, iteratedFDeriv ℝ k (elemLift g a b) (xt + sh v) ∂ν‖
        ≤ w * (M / w * ν.real Set.univ) := mul_le_mul_of_nonneg_left this hw
      _ = ν.real Set.univ * M := by field_simp

lemma isRapidDecay_avgFun {g : ElemGroup m n r s d → ℂ} (hg : IsRapidDecay g) :
    IsRapidDecay (avgFun ν g) := by
  refine ⟨fun a b => (key hg a b).1, fun i j k => ?_⟩
  obtain ⟨C, hC⟩ := hg.2 i j k
  exact ⟨ν.real Set.univ * C, fun a b xt =>
    bound hg a b k xt _ C (by positivity) fun v => by
      have := hC a b (xt + sh v)
      simpa [sh] using this⟩

lemma integrable_slice {g : ElemGroup m n r s d → ℂ} (hg : IsRapidDecay g)
    (e : ElemGroup m n r s d) :
    Integrable (fun v : Fin n → ℝ =>
      g (e.1, e.2.1 + (fun j => ((v j : ℝ) : UnitAddCircle)), e.2.2)) ν := by
  obtain ⟨C, hC⟩ := hg.2 0 0 0
  obtain ⟨x, t, a, b⟩ := e
  obtain ⟨t', rfl⟩ : ∃ t' : Fin n → ℝ, (fun j => ((t' j : ℝ) : UnitAddCircle)) = t :=
    ⟨fun j => (t j).out, funext fun j => by
      simp only
      exact QuotientAddGroup.out_eq' (t j)⟩
  have heq : (fun v : Fin n → ℝ =>
      g ((x, (fun j => ((t' j : ℝ) : UnitAddCircle)), a, b).1,
        (x, (fun j => ((t' j : ℝ) : UnitAddCircle)), a, b).2.1 +
          (fun j => ((v j : ℝ) : UnitAddCircle)),
        (x, (fun j => ((t' j : ℝ) : UnitAddCircle)), a, b).2.2)) =
      fun v => elemLift g a b ((x, t') + sh v) := by
    funext v
    simp only [elemLift, sh, Prod.fst_add, Prod.snd_add, add_zero, Pi.add_apply,
      AddCircle.coe_add]
    rfl
  rw [heq]
  refine Integrable.of_bound
    ((hg.1 a b).continuous.comp (continuous_const.add
      (continuous_const.prodMk continuous_id))).aestronglyMeasurable C
    (Eventually.of_forall fun v => ?_)
  simpa using hC a b ((x, t') + sh v)

variable (ν)

noncomputable def avgLin : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d where
  toFun g := ⟨avgFun ν g.toFun,
    Submodule.subset_span (isRapidDecay_avgFun (isRapidDecay_elemSchwartz_toFun g))⟩
  map_add' g h := by
    apply Subtype.ext
    funext e
    show avgFun ν (g.toFun + h.toFun) e = avgFun ν g.toFun e + avgFun ν h.toFun e
    simp only [avgFun, Pi.add_apply]
    exact integral_add (integrable_slice (isRapidDecay_elemSchwartz_toFun g) e)
      (integrable_slice (isRapidDecay_elemSchwartz_toFun h) e)
  map_smul' c g := by
    refine Subtype.ext (funext fun e => ?_)
    change avgFun ν (fun x => c * g.toFun x) e = c * avgFun ν g.toFun e
    exact integral_const_mul c _

theorem main :
    ∃ A : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous A ∧
      ∀ (g : ElemSchwartz m n r s d) (e : ElemGroup m n r s d),
        (A g).toFun e =
          ∫ v, g.toFun (e.1, e.2.1 + (fun j => ((v j : ℝ) : UnitAddCircle)), e.2.2) ∂ν := by
  refine ⟨avgLin ν, ?_, fun g e => rfl⟩
  have := elemSchwartz_continuous_of_seminorm_bound
    (avgLin (m := m) (r := r) (s := s) (d := d) ν).toAddMonoidHom
    (fun p => ⟨{p}, ν.real Set.univ, fun g M hM a b xt => by
      have hM' := hM p (Finset.mem_singleton_self p)
      have hb := bound (ν := ν) (isRapidDecay_elemSchwartz_toFun g) a b p.2.2 xt
        (‖a‖ ^ p.2.1 * ‖xt.1‖ ^ p.1) M (by positivity)
        fun v => by have := hM' a b (xt + sh v); rwa [fst_add_sh] at this
      exact hb⟩)
  exact this

end MasulloGRHAvgAux

open MeasureTheory MasulloGRH in
theorem solution {m n r s : ℕ} {d : Fin s → ℕ}
    (ν : Measure (Fin n → ℝ)) [IsFiniteMeasure ν] :
    ∃ A : ElemSchwartz m n r s d →ₗ[ℂ] ElemSchwartz m n r s d, Continuous A ∧
      ∀ (g : ElemSchwartz m n r s d) (e : ElemGroup m n r s d),
        (A g).toFun e =
          ∫ v, g.toFun (e.1, e.2.1 + (fun j => ((v j : ℝ) : UnitAddCircle)), e.2.2) ∂ν :=
  MasulloGRHAvgAux.main ν
