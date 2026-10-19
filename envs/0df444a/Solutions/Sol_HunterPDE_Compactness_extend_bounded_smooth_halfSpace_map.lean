-- Prove2me | solution 1 for HunterPDE.Compactness.extend_bounded_smooth_halfSpace_map
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-17T22:05:01.071016+00:00
-- url     : https://prove2.me/submissions/e1c7c77e-a909-443d-84a0-6aa3e286ddb7

import Theorems.Thm_HunterPDE_Compactness_exists_sobolev_seminorm
import Theorems.Thm_HunterPDE_Compactness_IsSmoothCompactClosedHalfSpace_memW
import Theorems.Thm_Seminorm_exists_bounded_extension_from_dense_submodule
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Tactic.FunProp

open MeasureTheory HunterPDE.Compactness
open scoped ENNReal NNReal
set_option autoImplicit false

theorem solution {m k d : ℕ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (C : ℝ≥0)
    (R : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ)
    (hdense : ∀ f, MemW k p (upperHalfSpace m) f →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ φ, IsSmoothCompactClosedHalfSpace φ ∧
        sobolevNorm k p (upperHalfSpace m) (f - φ) < ε)
    (hlinear : ∀ f g, IsSmoothCompactClosedHalfSpace f →
      IsSmoothCompactClosedHalfSpace g → ∀ a b : ℝ,
        R (a • f + b • g) =ᵐ[volume] a • R f + b • R g)
    (hbound : ∀ f, IsSmoothCompactClosedHalfSpace f →
      MemLp (R f) p volume ∧ eLpNorm (R f) p volume ≤
        (C : ℝ≥0∞) * sobolevNorm k p (upperHalfSpace m) f) :
    ∃ T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ,
      (∀ f g, MemW k p (upperHalfSpace m) f → MemW k p (upperHalfSpace m) g →
        ∀ a b : ℝ, T (a • f + b • g) =ᵐ[volume] a • T f + b • T g) ∧
      (∀ f, MemW k p (upperHalfSpace m) f →
        MemLp (T f) p volume ∧ eLpNorm (T f) p volume ≤
          (C : ℝ≥0∞) * sobolevNorm k p (upperHalfSpace m) f) ∧
      (∀ f, IsSmoothCompactClosedHalfSpace f → T f =ᵐ[volume] R f) := by
  classical
  letI : Fact (1 ≤ p) := ⟨hp⟩
  have hopen : IsOpen (upperHalfSpace m) := isOpen_lt continuous_const (by fun_prop)
  obtain ⟨W, hW, q, hq⟩ := exists_sobolev_seminorm (k := k) hp hp' _ hopen
  have hw (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)
      (hf : IsSmoothCompactClosedHalfSpace f) : f ∈ W :=
    (hW f).mpr (hf.memW hp hp')
  let S : Submodule ℝ W := {
    carrier := {f | IsSmoothCompactClosedHalfSpace (f : EuclideanSpace ℝ (Fin (m + 1)) → ℝ)}
    zero_mem' := ⟨contDiffOn_const, ∅, isCompact_empty, by simp⟩
    add_mem' := by
      rintro f g ⟨hf, K, hK, hz⟩ ⟨hg, L, hL, hw⟩
      refine ⟨hf.add hg, K ∪ L, hK.union hL, ?_⟩
      intro x hx hxl
      have hxl' : x ∉ K ∧ x ∉ L := ⟨fun h => hxl (Or.inl h), fun h => hxl (Or.inr h)⟩
      simp [hz x hx hxl'.1, hw x hx hxl'.2]
    smul_mem' := by
      rintro a f ⟨hf, K, hK, hz⟩
      refine ⟨hf.const_smul a, K, hK, ?_⟩
      intro x hx hxl
      simp [hz x hx hxl] }
  have hS (f : S) : IsSmoothCompactClosedHalfSpace (f : W).val := f.property
  let r : S →ₗ[ℝ] Lp ℝ p (volume : Measure (EuclideanSpace ℝ (Fin d))) := {
    toFun := fun f => (hbound _ (hS f)).1.toLp (R (f : W).val)
    map_add' := by
      intro f g
      apply Lp.ext
      filter_upwards [(hbound _ (hS (f + g))).1.coeFn_toLp,
        Lp.coeFn_add ((hbound _ (hS f)).1.toLp _) ((hbound _ (hS g)).1.toLp _),
        (hbound _ (hS f)).1.coeFn_toLp, (hbound _ (hS g)).1.coeFn_toLp,
        hlinear _ _ (hS f) (hS g) 1 1] with x hfg hadd hf hg hlin
      change ((hbound _ (hS (f + g))).1.toLp _ : EuclideanSpace ℝ (Fin d) → ℝ) x = _
      calc
        _ = R ((f + g : S) : W).val x := hfg
        _ = R (f : W).val x + R (g : W).val x := by simpa using hlin
        _ = _ := by rw [hadd]; simp only [Pi.add_apply, hf, hg]
    map_smul' := by
      intro a f
      apply Lp.ext
      filter_upwards [(hbound _ (hS (a • f))).1.coeFn_toLp,
        Lp.coeFn_smul a ((hbound _ (hS f)).1.toLp _),
        (hbound _ (hS f)).1.coeFn_toLp,
        hlinear _ _ (hS f) (hS f) a 0] with x haf hsmul hf hlin
      change ((hbound _ (hS (a • f))).1.toLp _ : EuclideanSpace ℝ (Fin d) → ℝ) x = _
      calc
        _ = R ((a • f : S) : W).val x := haf
        _ = a * R (f : W).val x := by simpa using hlin
        _ = _ := by simp only [RingHom.id_apply]; rw [hsmul]; simp only [Pi.smul_apply, smul_eq_mul, hf] }
  have hd : ∀ f : W, ∀ ε : ℝ, 0 < ε → ∃ φ : S, q (f - φ) < ε := by
    intro f ε hε
    obtain ⟨φ, hφ, herr⟩ := hdense f ((hW f).mp f.property)
      (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε)
    let ψ : S := ⟨⟨φ, hw φ hφ⟩, hφ⟩
    refine ⟨ψ, ?_⟩
    have hnorm := hq (f - (ψ : W))
    change sobolevNorm k p (upperHalfSpace m) ((f - (ψ : W) : W).val) < ENNReal.ofReal ε at herr
    rw [← hnorm] at herr
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mp herr
  have hb : ∀ f : S, ‖r f‖ ≤ (C : ℝ) * q f := by
    intro f
    have he := (hbound _ (hS f)).2
    rw [← hq (f : W)] at he
    have ht := ENNReal.toReal_mono (by finiteness) he
    simpa [r, Lp.norm_toLp, ENNReal.toReal_mul, ENNReal.toReal_ofReal (apply_nonneg q _)] using ht
  obtain ⟨A, hA, hagree⟩ := q.exists_bounded_extension_from_dense_submodule S r C hd hb
  let T : (EuclideanSpace ℝ (Fin (m + 1)) → ℝ) → EuclideanSpace ℝ (Fin d) → ℝ :=
    fun f => if hf : f ∈ W then (A ⟨f, hf⟩ : EuclideanSpace ℝ (Fin d) → ℝ) else 0
  have hT (f : W) : T f = (A f : EuclideanSpace ℝ (Fin d) → ℝ) := by simp [T]
  refine ⟨T, ?_, ?_, ?_⟩
  · intro f g hf hg a b
    let u : W := ⟨f, (hW f).mpr hf⟩
    let v : W := ⟨g, (hW g).mpr hg⟩
    change T ((a • u + b • v : W).val) =ᵐ[volume] a • T u.val + b • T v.val
    rw [hT, hT, hT, map_add, map_smul, map_smul]
    exact (Lp.coeFn_add _ _).trans ((Lp.coeFn_smul a _).add (Lp.coeFn_smul b _))
  · intro f hf
    let u : W := ⟨f, (hW f).mpr hf⟩
    change MemLp (T u.val) p volume ∧ _
    rw [hT]
    refine ⟨Lp.memLp (A u), ?_⟩
    rw [← Lp.enorm_def, ← hq u]
    have he := ENNReal.ofReal_le_ofReal (hA u)
    simpa [ENNReal.ofReal_mul C.coe_nonneg, ofReal_norm] using he
  · intro f hf
    let u : S := ⟨⟨f, hw f hf⟩, hf⟩
    change T ((u : W).val) =ᵐ[volume] R ((u : W).val)
    rw [hT, hagree u]
    exact (hbound _ (hS u)).1.coeFn_toLp

