-- Prove2me | solution 1 for MonotoneCompStatics.QSMChar.Supplement.theorem3
-- status  : ACCEPTED   (prove)
-- author  : @mikedeng1
-- created : 2026-11-27T06:29:23.266273+00:00
-- url     : https://prove2.me/submissions/6520c1f2-becf-45f8-bb27-b967cfe60e63

import Mathlib
import Definitions.Def_MonotoneCompStatics_QSMChar_Supplement_Utility

open MonotoneCompStatics
open MonotoneCompStatics.QSMChar
open MonotoneCompStatics.QSMChar.Supplement

/-- Corrected: weak equivalence, strict sufficient direction, and a counterexample
to the printed strict necessary direction, without adding a nonzero U_x premise. -/
theorem solution (U : ℝ → ℝ → ℝ → ℝ) (hreg : CompletelyRegular U)
    (h2 : ContDiff ℝ 2 (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2))
    (hy : ∀ x y t : ℝ, deriv (fun b => U x b t) y ≠ 0) :
    (LexSingleCrossing U ↔ SpenceMirrlees U) ∧
    (StrictSpenceMirrlees U → LexStrictSingleCrossing U) ∧
    (CompletelyRegular cubicUtility ∧
      ContDiff ℝ 2 (fun p : (ℝ × ℝ) × ℝ => cubicUtility p.1.1 p.1.2 p.2) ∧
      (∀ x y t : ℝ, deriv (fun b => cubicUtility x b t) y ≠ 0) ∧
      LexStrictSingleCrossing cubicUtility ∧ ¬ StrictSpenceMirrlees cubicUtility) := by
        -- Part 3
        have hcub : CompletelyRegular cubicUtility ∧
            ContDiff ℝ 2 (fun p : (ℝ × ℝ) × ℝ => cubicUtility p.1.1 p.1.2 p.2) ∧
            (∀ x y t : ℝ, deriv (fun b => cubicUtility x b t) y ≠ 0) ∧
            LexStrictSingleCrossing cubicUtility ∧ ¬ StrictSpenceMirrlees cubicUtility := by
          have hdy : ∀ x y t : ℝ, deriv (fun b => cubicUtility x b t) y = 1 := by
            intro x y t
            simp [cubicUtility]
          refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
          · unfold cubicUtility; fun_prop
          · intro t c
            right
            have : {p : ℝ × ℝ | cubicUtility p.1 p.2 t = c} = Set.range (fun s : ℝ => (s, c - t * s ^ 3)) := by
              ext ⟨a, b⟩
              simp only [cubicUtility, Set.mem_setOf_eq, Set.mem_range, Prod.mk.injEq]
              constructor
              · intro h; exact ⟨a, rfl, by linarith⟩
              · rintro ⟨s, rfl, rfl⟩; ring
            rw [this]
            exact isPathConnected_range (by fun_prop)
          · unfold cubicUtility; fun_prop
          · intro x y t; rw [hdy]; norm_num
          · intro p' p'' hlt t' t'' ht h
            simp only [cubicUtility] at h ⊢
            rcases Prod.Lex.lt_iff.mp hlt with h1 | ⟨h1, h1'⟩
            · have h3 : (ofLex p'').1 ^ 3 < (ofLex p').1 ^ 3 := by
                exact Odd.strictMono_pow (by decide) h1
              nlinarith
            · rw [h1] at h ⊢; linarith
          · intro h
            have h0 := h 0 0 (show (0:ℝ) < 1 by norm_num)
            simp [marginalRatio, cubicUtility] at h0
        have hF1 : ContDiff ℝ 1 (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) := hreg.1
        have hDF : ∀ q : (ℝ × ℝ) × ℝ, HasFDerivAt (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2)
            (fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) q) q :=
          fun q => ((hF1.differentiable (by norm_num)) q).hasFDerivAt
        have hdir : ∀ x y t s : ℝ, HasDerivAt (fun h => U (x + h) (y + s * h) t)
            (deriv (fun a => U a y t) x + s * deriv (fun b => U x b t) y) 0 := by
          intro x y t s
          set L := fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) ((x, y), t)
          have hx : HasDerivAt (fun a => U a y t) (L ((1, 0), 0)) x := by
            have : HasDerivAt (fun a : ℝ => (((a, y), t) : (ℝ × ℝ) × ℝ)) ((1, 0), 0) x :=
              ((hasDerivAt_id x).prodMk (hasDerivAt_const x y)).prodMk (hasDerivAt_const x t)
            exact (hDF ((x, y), t)).comp_hasDerivAt x this
          have hyd : HasDerivAt (fun b => U x b t) (L ((0, 1), 0)) y := by
            have : HasDerivAt (fun b : ℝ => (((x, b), t) : (ℝ × ℝ) × ℝ)) ((0, 1), 0) y :=
              ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)).prodMk (hasDerivAt_const y t)
            exact (hDF ((x, y), t)).comp_hasDerivAt y this
          have hg : HasDerivAt (fun h : ℝ => (((x + h, y + s * h), t) : (ℝ × ℝ) × ℝ)) ((1, s), 0) 0 := by
            have h1 : HasDerivAt (fun h : ℝ => x + h) 1 0 := by
              simpa using (hasDerivAt_id (0:ℝ)).const_add x
            have h2 : HasDerivAt (fun h : ℝ => y + s * h) s 0 := by
              simpa using ((hasDerivAt_id (0:ℝ)).const_mul s).const_add y
            exact (h1.prodMk h2).prodMk (hasDerivAt_const (0:ℝ) t)
          have hg' := (hDF ((x + 0, y + s * 0), t)).comp_hasDerivAt (0:ℝ) hg
          simp only [add_zero, mul_zero] at hg'
          have hL : L ((1, s), 0) = L ((1, 0), 0) + s * L ((0, 1), 0) := by
            have e : (((1, s), 0) : (ℝ × ℝ) × ℝ) = ((1, 0), 0) + s • ((0, 1), 0) := by
              ext <;> simp
            rw [e, map_add, map_smul, smul_eq_mul]
          rw [hx.deriv, hyd.deriv, ← hL]
          exact hg'
        -- SC → SM
        have hnec : LexSingleCrossing U → SpenceMirrlees U := by
          intro hSC x y t₁ t₂ ht
          rcases eq_or_lt_of_le ht with heq | hlt
          · rw [heq]
          set a1 := deriv (fun a => U a y t₁) x
          set b1 := deriv (fun b => U x b t₁) y
          set a2 := deriv (fun a => U a y t₂) x
          set b2 := deriv (fun b => U x b t₂) y
          have key : ∀ s : ℝ, 0 < a1 + s * b1 → 0 ≤ a2 + s * b2 := by
            intro s hs
            have d1 := hasDerivAt_iff_tendsto_slope.mp (hdir x y t₁ s)
            have d2 := hasDerivAt_iff_tendsto_slope.mp (hdir x y t₂ s)
            have d1' := d1.mono_left (nhdsGT_le_nhdsNE (0:ℝ))
            have d2' := d2.mono_left (nhdsGT_le_nhdsNE (0:ℝ))
            have ev1 : ∀ᶠ h in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 < slope (fun h => U (x + h) (y + s * h) t₁) 0 h :=
              d1'.eventually (lt_mem_nhds hs)
            have ev2 : ∀ᶠ h in nhdsWithin (0:ℝ) (Set.Ioi 0), 0 ≤ slope (fun h => U (x + h) (y + s * h) t₂) 0 h := by
              filter_upwards [ev1, self_mem_nhdsWithin] with h hh hpos
              have hpos' : (0:ℝ) < h := hpos
              rw [slope_def_field] at hh ⊢
              simp only [add_zero, mul_zero, sub_zero] at hh ⊢
              have hle : U x y t₁ < U (x + h) (y + s * h) t₁ := by
                have := (div_pos_iff_of_pos_right hpos').mp hh; linarith
              have hl : toLex (x, y) < toLex (x + h, y + s * h) :=
                Prod.Lex.toLex_lt_toLex.mpr (Or.inl (by linarith))
              have := (hSC hl hlt).2 hle.le
              simp only [ofLex_toLex] at this
              apply div_nonneg _ hpos'.le
              linarith
            exact ge_of_tendsto d2' ev2
          have hb1 := hy x y t₁
          have hb2 := hy x y t₂
          show a1 / |b1| ≤ a2 / |b2|
          have hB1 : 0 < |b1| := abs_pos.mpr hb1
          have hB2 : 0 < |b2| := abs_pos.mpr hb2
          have e1 : a1 = a1 / |b1| * |b1| := (div_mul_cancel₀ a1 hB1.ne').symm
          have e2 : a2 = a2 / |b2| * |b2| := (div_mul_cancel₀ a2 hB2.ne').symm
          set ρ1 := a1 / |b1|
          set ρ2 := a2 / |b2|
          set B1 := |b1|
          set B2 := |b2|
          by_contra hcon
          have hc : ρ2 < ρ1 := lt_of_not_ge hcon
          have hsub : 0 < ρ1 - ρ2 := sub_pos.mpr hc
          rcases lt_or_gt_of_ne hb1 with hb1n | hb1p <;> rcases lt_or_gt_of_ne hb2 with hb2n | hb2p
          · have q1 : b1 = -B1 := by rw [show B1 = |b1| from rfl, abs_of_neg hb1n]; ring
            have q2 : b2 = -B2 := by rw [show B2 = |b2| from rfl, abs_of_neg hb2n]; ring
            have k := key ((ρ1 + ρ2) / 2) (by
              have : a1 + (ρ1 + ρ2) / 2 * b1 = B1 * ((ρ1 - ρ2) / 2) := by rw [e1, q1]; ring
              rw [this]; positivity)
            have : a2 + (ρ1 + ρ2) / 2 * b2 = -(B2 * ((ρ1 - ρ2) / 2)) := by rw [e2, q2]; ring
            rw [this] at k
            have : 0 < B2 * ((ρ1 - ρ2) / 2) := by positivity
            linarith
          · have q1 : b1 = -B1 := by rw [show B1 = |b1| from rfl, abs_of_neg hb1n]; ring
            have q2 : b2 = B2 := by rw [show B2 = |b2| from rfl, abs_of_pos hb2p]
            set s := -(|ρ1| + |ρ2| + 1)
            have k := key s (by
              have : a1 + s * b1 = B1 * (ρ1 + |ρ1| + |ρ2| + 1) := by rw [e1, q1]; ring
              rw [this]; have := neg_abs_le ρ1; have := abs_nonneg ρ2
              apply mul_pos hB1; linarith)
            have : a2 + s * b2 = -(B2 * (|ρ1| + |ρ2| + 1 - ρ2)) := by rw [e2, q2]; ring
            rw [this] at k
            have : 0 < B2 * (|ρ1| + |ρ2| + 1 - ρ2) := by
              have := le_abs_self ρ2; have := abs_nonneg ρ1
              apply mul_pos hB2; linarith
            linarith
          · have q1 : b1 = B1 := by rw [show B1 = |b1| from rfl, abs_of_pos hb1p]
            have q2 : b2 = -B2 := by rw [show B2 = |b2| from rfl, abs_of_neg hb2n]; ring
            set s := (|ρ1| + |ρ2| + 1)
            have k := key s (by
              have : a1 + s * b1 = B1 * (ρ1 + |ρ1| + |ρ2| + 1) := by rw [e1, q1]; ring
              rw [this]; have := neg_abs_le ρ1; have := abs_nonneg ρ2
              apply mul_pos hB1; linarith)
            have : a2 + s * b2 = -(B2 * (|ρ1| + |ρ2| + 1 - ρ2)) := by rw [e2, q2]; ring
            rw [this] at k
            have : 0 < B2 * (|ρ1| + |ρ2| + 1 - ρ2) := by
              have := le_abs_self ρ2; have := abs_nonneg ρ1
              apply mul_pos hB2; linarith
            linarith
          · have q1 : b1 = B1 := by rw [show B1 = |b1| from rfl, abs_of_pos hb1p]
            have q2 : b2 = B2 := by rw [show B2 = |b2| from rfl, abs_of_pos hb2p]
            have k := key (-((ρ1 + ρ2) / 2)) (by
              have : a1 + -((ρ1 + ρ2) / 2) * b1 = B1 * ((ρ1 - ρ2) / 2) := by rw [e1, q1]; ring
              rw [this]; positivity)
            have : a2 + -((ρ1 + ρ2) / 2) * b2 = -(B2 * ((ρ1 - ρ2) / 2)) := by rw [e2, q2]; ring
            rw [this] at k
            have : 0 < B2 * ((ρ1 - ρ2) / 2) := by positivity
            linarith
        -- partial derivative in y as a continuous function
        have hyform : ∀ x y t : ℝ, deriv (fun b => U x b t) y =
            fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) ((x, y), t) ((0, 1), 0) := by
          intro x y t
          have : HasDerivAt (fun b : ℝ => (((x, b), t) : (ℝ × ℝ) × ℝ)) ((0, 1), 0) y :=
            ((hasDerivAt_const y x).prodMk (hasDerivAt_id y)).prodMk (hasDerivAt_const y t)
          exact ((hDF ((x, y), t)).comp_hasDerivAt y this).deriv
        have hcont : Continuous (fun q : (ℝ × ℝ) × ℝ =>
            fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) q ((0, 1), 0)) :=
          (hF1.continuous_fderiv (by norm_num)).clm_apply continuous_const
        have hsign : (∀ x y t : ℝ, 0 < deriv (fun b => U x b t) y) ∨
            (∀ x y t : ℝ, deriv (fun b => U x b t) y < 0) := by
          by_contra hcon
          push_neg at hcon
          obtain ⟨⟨x1, y1, t1, h1⟩, ⟨x2, y2, t2, h2'⟩⟩ := hcon
          have h1' : deriv (fun b => U x1 b t1) y1 < 0 := lt_of_le_of_ne h1 (hy _ _ _)
          have h2'' : 0 < deriv (fun b => U x2 b t2) y2 := lt_of_le_of_ne h2' (hy _ _ _).symm
          have hpc := (isPreconnected_univ (α := (ℝ × ℝ) × ℝ)).image _ hcont.continuousOn
          have hm1 : deriv (fun b => U x1 b t1) y1 ∈ (fun q : (ℝ × ℝ) × ℝ =>
            fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) q ((0, 1), 0)) '' Set.univ :=
            ⟨((x1, y1), t1), trivial, (hyform _ _ _).symm⟩
          have hm2 : deriv (fun b => U x2 b t2) y2 ∈ (fun q : (ℝ × ℝ) × ℝ =>
            fderiv ℝ (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) q ((0, 1), 0)) '' Set.univ :=
            ⟨((x2, y2), t2), trivial, (hyform _ _ _).symm⟩
          obtain ⟨q, -, hq⟩ := hpc.Icc_subset hm1 hm2 ⟨h1'.le, h2''.le⟩
          obtain ⟨⟨a, b⟩, c⟩ := q
          exact hy a b c (by rw [hyform]; exact hq)
        -- monotonicity in y
        have hmono : (∀ x t : ℝ, StrictMono (fun b => U x b t)) ∨ (∀ x t : ℝ, StrictAnti (fun b => U x b t)) := by
          rcases hsign with h | h
          · left; intro x t; exact strictMono_of_deriv_pos (fun y => h x y t)
          · right; intro x t; exact strictAnti_of_deriv_neg (fun y => h x y t)
        have core : ∀ (strict : Prop) (f g : ℝ → ℝ → ℝ),
          (∀ x y, ∃ L L' : ℝ × ℝ →L[ℝ] ℝ, HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) L (x, y) ∧
             HasFDerivAt (fun p : ℝ × ℝ => g p.1 p.2) L' (x, y) ∧ 0 < L (0,1) ∧ 0 < L' (0,1) ∧
             L (1,0) / L (0,1) ≤ L' (1,0) / L' (0,1) ∧ (strict → L (1,0) / L (0,1) < L' (1,0) / L' (0,1))) →
          (∀ c, {p : ℝ × ℝ | f p.1 p.2 = c} = ∅ ∨ IsPathConnected {p : ℝ × ℝ | f p.1 p.2 = c}) →
          ∀ x₁ y₁ x₂ y₂, x₁ < x₂ → f x₁ y₁ ≤ f x₂ y₂ →
            g x₁ y₁ ≤ g x₂ y₂ ∧ (f x₁ y₁ < f x₂ y₂ → g x₁ y₁ < g x₂ y₂) ∧ (strict → g x₁ y₁ < g x₂ y₂)  := by
          intro strict f g hD hpc
          have hFc : Continuous (fun p : ℝ × ℝ => f p.1 p.2) := continuous_iff_continuousAt.2 fun p =>
            (hD p.1 p.2).choose_spec.choose_spec.1.continuousAt
          have hGc : Continuous (fun p : ℝ × ℝ => g p.1 p.2) := continuous_iff_continuousAt.2 fun p =>
            (hD p.1 p.2).choose_spec.choose_spec.2.1.continuousAt
          have hfx : ∀ y, Continuous (fun a => f a y) := fun y =>
            hFc.comp (continuous_id.prodMk continuous_const)
          have hgx : ∀ y, Continuous (fun a => g a y) := fun y =>
            hGc.comp (continuous_id.prodMk continuous_const)
          have hfy : ∀ x, Continuous (fun b => f x b) := fun x =>
            hFc.comp (continuous_const.prodMk continuous_id)
          have hvert : ∀ x y : ℝ, ∀ L : ℝ × ℝ →L[ℝ] ℝ, ∀ F : ℝ × ℝ → ℝ, HasFDerivAt F L (x, y) →
              HasDerivAt (fun b => F (x, b)) (L (0,1)) y := by
            intro x y L F hF
            have : HasDerivAt (fun b : ℝ => ((x, b) : ℝ × ℝ)) (0, 1) y :=
              (hasDerivAt_const y x).prodMk (hasDerivAt_id y)
            exact hF.comp_hasDerivAt y this
          have hfm : ∀ x, StrictMono (fun b => f x b) := by
            intro x
            exact strictMono_of_hasDerivAt_pos (f' := fun y => (hD x y).choose (0,1))
              (fun y => hvert x y _ _ (hD x y).choose_spec.choose_spec.1)
              (fun y => (hD x y).choose_spec.choose_spec.2.2.1)
          have hgm : ∀ x, StrictMono (fun b => g x b) := by
            intro x
            exact strictMono_of_hasDerivAt_pos (f' := fun y => (hD x y).choose_spec.choose (0,1))
              (fun y => hvert x y _ _ (hD x y).choose_spec.choose_spec.2.1)
              (fun y => (hD x y).choose_spec.choose_spec.2.2.2.1)
          -- local solvability
          have hloc : ∀ x y ε : ℝ, 0 < ε → ∀ᶠ x' in nhds x, ∃ y', |y' - y| < ε ∧ f x' y' = f x y := by
            intro x y ε hε
            have h1 : f x (y - ε/2) < f x y := hfm x (by linarith)
            have h2 : f x y < f x (y + ε/2) := hfm x (by linarith)
            filter_upwards [(hfx (y - ε/2)).continuousAt.eventually (gt_mem_nhds h1),
              (hfx (y + ε/2)).continuousAt.eventually (lt_mem_nhds h2)] with x' hx1 hx2
            obtain ⟨y', hy', hfy'⟩ := intermediate_value_Ioo (show y - ε/2 ≤ y + ε/2 by linarith)
              (hfy x').continuousOn ⟨hx1, hx2⟩
            refine ⟨y', ?_, hfy'⟩
            rw [abs_lt]; constructor <;> linarith [hy'.1, hy'.2]
          -- projections are order connected
          have hconn : ∀ w a b ya yb, f a ya = w → f b yb = w → Set.Icc a b ⊆ {x | ∃ y, f x y = w} := by
            intro w a b ya yb ha hb
            have hS : IsPreconnected (Prod.fst '' {p : ℝ × ℝ | f p.1 p.2 = w}) := by
              rcases hpc w with h | h
              · have : (a, ya) ∈ {p : ℝ × ℝ | f p.1 p.2 = w} := ha
                rw [h] at this; exact absurd this (Set.notMem_empty _)
              · exact h.isConnected.isPreconnected.image _ continuous_fst.continuousOn
            intro x hx
            obtain ⟨p, hp, rfl⟩ := hS.Icc_subset (a := a) (b := b) ⟨(a, ya), ha, rfl⟩ ⟨(b, yb), hb, rfl⟩ hx
            exact ⟨p.2, hp⟩
          have hF2 : ∀ w a b ya yb, a < b → f a ya = w → f b yb = w →
              g a ya ≤ g b yb ∧ (strict → g a ya < g b yb) := by
            intro w a b ya yb hab ha hb
            have hP := hconn w a b ya yb ha hb
            classical
            let φ : ℝ → ℝ := fun x => if h : ∃ y, f x y = w then h.choose else 0
            have hφ : ∀ x, (∃ y, f x y = w) → f x (φ x) = w := by
              intro x hx; simp only [φ, dif_pos hx]; exact hx.choose_spec
            have huniq : ∀ x y, f x y = w → φ x = y := by
              intro x y h; exact (hfm x).injective ((hφ x ⟨y, h⟩).trans h.symm)
            have hφd : ∀ x₀, (∃ y, f x₀ y = w) → ∀ L : ℝ × ℝ →L[ℝ] ℝ,
                HasFDerivAt (fun p : ℝ × ℝ => f p.1 p.2) L (x₀, φ x₀) → 0 < L (0,1) →
                HasDerivAt φ (-(L (1,0) / L (0,1))) x₀ := by
              intro x₀ hx₀ L hL hB
              set y₀ := φ x₀ with hy₀
              have hw : f x₀ y₀ = w := hφ x₀ hx₀
              set A := L (1,0)
              set B := L (0,1)
              have hev : ∀ ε > 0, ∀ᶠ h in nhds (0:ℝ), (∃ y, f (x₀ + h) y = w) ∧ |φ (x₀ + h) - y₀| < ε := by
                intro ε hε
                have ht : Filter.Tendsto (fun h : ℝ => x₀ + h) (nhds 0) (nhds x₀) := by
                  have := (continuous_const_add x₀).tendsto 0; simpa using this
                filter_upwards [ht.eventually (hloc x₀ y₀ ε hε)] with h ⟨y', hy', hfy'⟩
                rw [hw] at hfy'
                exact ⟨⟨y', hfy'⟩, by rw [huniq _ _ hfy']; exact hy'⟩
              have hk : Filter.Tendsto (fun h : ℝ => ((h, φ (x₀ + h) - y₀) : ℝ × ℝ)) (nhds 0) (nhds 0) := by
                rw [show (0 : ℝ × ℝ) = ((0:ℝ), (0:ℝ)) from rfl]
                refine Filter.Tendsto.prodMk_nhds Filter.tendsto_id ?_
                rw [Metric.tendsto_nhds]
                intro ε hε
                filter_upwards [hev ε hε] with h hh
                simpa [Real.dist_eq] using hh.2
              have hlo := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hL).comp_tendsto hk
              rw [hasDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
              intro c hc
              set C := (B + 2*|A|)/B
              have hC : 0 < 1 + C := by positivity
              set ε := min (B/2) (c*B/(1+C))
              have hε : 0 < ε := lt_min (by linarith) (by positivity)
              filter_upwards [Asymptotics.isLittleO_iff.mp hlo hε, hev 1 one_pos] with h h1 h2
              simp only [Function.comp] at h1
              set k := φ (x₀ + h) - y₀ with hkdef
              have hfe : f (x₀ + h) (y₀ + k) = w := by
                rw [hkdef, add_sub_cancel]; exact hφ _ h2.1
              have hLk : L (h, k) = A * h + B * k := by
                have : ((h, k) : ℝ × ℝ) = h • ((1:ℝ),(0:ℝ)) + k • ((0:ℝ),(1:ℝ)) := by ext <;> simp
                rw [this, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]; ring
              have h1' : |A * h + B * k| ≤ ε * (|h| + |k|) := by
                have hn : ‖((h, k) : ℝ × ℝ)‖ ≤ |h| + |k| := by
                  rw [Prod.norm_def]; simp only [Real.norm_eq_abs]
                  exact max_le (by linarith [abs_nonneg k]) (by linarith [abs_nonneg h])
                have := h1
                simp only [Prod.fst_add, Prod.snd_add, hfe, hw, sub_self, zero_sub, norm_neg, hLk,
                  Real.norm_eq_abs] at this
                calc |A * h + B * k| ≤ ε * ‖((h, k) : ℝ × ℝ)‖ := this
                  _ ≤ ε * (|h| + |k|) := mul_le_mul_of_nonneg_left hn hε.le
              have hεB : ε ≤ B/2 := min_le_left _ _
              have hεc : ε * (1 + C) ≤ c * B := (le_div_iff₀ hC).mp (min_le_right _ _)
              have habs1 : B * |k| ≤ |A * h + B * k| + |A| * |h| := by
                have : |B * k| ≤ |A * h + B * k| + |A * h| := by
                  calc |B * k| = |(A * h + B * k) + (-(A * h))| := by ring_nf
                    _ ≤ |A * h + B * k| + |-(A * h)| := abs_add_le _ _
                    _ = |A * h + B * k| + |A * h| := by rw [abs_neg]
                rw [abs_mul, abs_mul, abs_of_pos hB] at this; exact this
              have hk1 : B * |k| ≤ (B + 2*|A|) * |h| := by
                have e1 : ε * |k| ≤ B/2 * |k| := mul_le_mul_of_nonneg_right hεB (abs_nonneg k)
                have e2 : ε * |h| ≤ B/2 * |h| := mul_le_mul_of_nonneg_right hεB (abs_nonneg h)
                linarith
              have hkC : |k| ≤ C * |h| := by
                rw [div_mul_eq_mul_div, le_div_iff₀ hB]; linarith
              have hfin : |A * h + B * k| ≤ c * B * |h| := by
                calc |A * h + B * k| ≤ ε * (|h| + |k|) := h1'
                  _ ≤ ε * ((1 + C) * |h|) := mul_le_mul_of_nonneg_left (by linarith) hε.le
                  _ = (ε * (1 + C)) * |h| := by ring
                  _ ≤ (c * B) * |h| := mul_le_mul_of_nonneg_right hεc (abs_nonneg h)
              have he : k - h • (-(A / B)) = (A * h + B * k) / B := by
                rw [smul_eq_mul]; field_simp; ring
              rw [he, Real.norm_eq_abs, abs_div, abs_of_pos hB, div_le_iff₀ hB, Real.norm_eq_abs]
              linarith
            have hG : ∀ x₀ ∈ Set.Icc a b, ∃ D, HasDerivAt (fun x => g x (φ x)) D x₀ ∧ 0 ≤ D ∧ (strict → 0 < D) := by
              intro x₀ hx₀
              obtain ⟨L, L', hL, hL', hB, hB', hr, hrs⟩ := hD x₀ (φ x₀)
              have hd := hφd x₀ (hP hx₀) L hL hB
              have hc : HasDerivAt (fun x => ((x, φ x) : ℝ × ℝ)) ((1 : ℝ), -(L (1,0) / L (0,1))) x₀ :=
                (hasDerivAt_id x₀).prodMk hd
              have e : L' (1, -(L (1,0) / L (0,1))) = L' (1,0) - (L (1,0) / L (0,1)) * L' (0,1) := by
                have : ((1:ℝ), -(L (1,0) / L (0,1))) = ((1:ℝ),(0:ℝ)) + (-(L (1,0) / L (0,1))) • ((0:ℝ),(1:ℝ)) := by
                  ext <;> simp
                rw [this, map_add, map_smul, smul_eq_mul]; ring
              refine ⟨L' (1, -(L (1,0) / L (0,1))), by have := hL'.comp_hasDerivAt x₀ hc; exact this, ?_, ?_⟩
              · rw [e]; have := (le_div_iff₀ hB').mp hr; linarith
              · intro hs; rw [e]; have := (lt_div_iff₀ hB').mp (hrs hs); linarith
            have hcont : ContinuousOn (fun x => g x (φ x)) (Set.Icc a b) := fun x hx =>
              (hG x hx).choose_spec.1.continuousAt.continuousWithinAt
            have hφa : φ a = ya := huniq a ya ha
            have hφb : φ b = yb := huniq b yb hb
            have hint : interior (Set.Icc a b) ⊆ Set.Icc a b := interior_subset
            constructor
            · have hmon := monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont
                (fun x hx => (hG x (hint hx)).choose_spec.1.differentiableAt.differentiableWithinAt)
                (fun x hx => by rw [(hG x (hint hx)).choose_spec.1.deriv]; exact (hG x (hint hx)).choose_spec.2.1)
              have := hmon ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ hab.le
              dsimp only at this
              rw [hφa, hφb] at this; exact this
            · intro hs
              have hmon := strictMonoOn_of_deriv_pos (convex_Icc a b) hcont
                (fun x hx => by rw [(hG x (hint hx)).choose_spec.1.deriv]; exact (hG x (hint hx)).choose_spec.2.2 hs)
              have := hmon ⟨le_refl a, hab.le⟩ ⟨hab.le, le_refl b⟩ hab
              dsimp only at this
              rw [hφa, hφb] at this; exact this
          have hweak : ∀ x₁ y₁ x₂ y₂, x₁ < x₂ → f x₁ y₁ ≤ f x₂ y₂ → g x₁ y₁ ≤ g x₂ y₂ := by
            intro x₁ y₁ x₂ y₂ h12 hle
            set d := f x₂ y₂ with hd
            set e := g x₂ y₂ with he
            let T : Set ℝ := {x | ∀ y, f x y ≤ d → g x y ≤ e}
            have hT2 : x₂ ∈ T := fun y hy => (hgm x₂).monotone ((hfm x₂).le_iff_le.mp hy)
            by_contra hcon
            let Bd : Set ℝ := {x | x ∈ Set.Icc x₁ x₂ ∧ x ∉ T}
            have hx1B : x₁ ∈ Bd := ⟨⟨le_refl _, h12.le⟩, fun h => hcon (h y₁ hle)⟩
            have hBne : Bd.Nonempty := ⟨x₁, hx1B⟩
            have hBbdd : BddAbove Bd := ⟨x₂, fun x hx => hx.1.2⟩
            set s := sSup Bd with hsdef
            have hs1 : x₁ ≤ s := le_csSup hBbdd hx1B
            have hs2 : s ≤ x₂ := csSup_le hBne (fun x hx => hx.1.2)
            have hR : ∀ x, s < x → x ≤ x₂ → x ∈ T := by
              intro x hx hx2; by_contra hxT
              have := le_csSup hBbdd (show x ∈ Bd from ⟨⟨by linarith, hx2⟩, hxT⟩); linarith
            have hsT : s ∈ T := by
              rcases eq_or_lt_of_le hs2 with heq | hlt
              · rw [heq]; exact hT2
              intro y hy
              by_contra hgy; push_neg at hgy
              have hev := hloc s y 1 one_pos
              have hev2 : ∀ᶠ x in nhdsWithin s (Set.Ioi s), (∃ y', |y' - y| < 1 ∧ f x y' = f s y) ∧ x < x₂ :=
                (Filter.Eventually.filter_mono nhdsWithin_le_nhds hev).and (Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds hlt))
              obtain ⟨x, ⟨⟨y', -, hfy'⟩, hx2⟩, hxs⟩ := (hev2.and self_mem_nhdsWithin).exists
              have hxT := hR x hxs hx2.le
              have h1 := (hF2 (f s y) s x y y' hxs rfl hfy').1
              have h2 := hxT y' (by rw [hfy']; exact hy)
              linarith
            have hbad : ∀ δ > 0, ∃ x', s - δ < x' ∧ x' < s ∧ x₁ ≤ x' ∧ ∃ y', f x' y' ≤ d ∧ e < g x' y' := by
              intro δ hδ
              obtain ⟨x', ⟨hx'I, hx'T⟩, hx'⟩ := exists_lt_of_lt_csSup hBne (show s - δ < s by linarith)
              have hx's : x' ≤ s := le_csSup hBbdd ⟨hx'I, hx'T⟩
              have hne : x' ≠ s := fun h => hx'T (h ▸ hsT)
              simp only [T, Set.mem_setOf_eq] at hx'T
              push_neg at hx'T
              obtain ⟨y', hy1, hy2⟩ := hx'T
              exact ⟨x', hx', lt_of_le_of_ne hx's hne, hx'I.1, y', hy1, hy2⟩
            have hii : ∀ x' y', x' < s → f x' y' ≤ d → e < g x' y' →
                ∀ x Y, s ≤ x → x ≤ x₂ → f x' y' ≤ f x Y := by
              intro x' y' hx's hfd hge x Y hsx hx2
              by_contra hlt; push_neg at hlt
              let γ : ℝ → ℝ × ℝ := fun τ => (x + τ * (x₂ - x), Y + τ * (y₂ - Y))
              have hγc : Continuous γ := by fun_prop
              obtain ⟨τ, hτ, hτv⟩ := intermediate_value_Icc zero_le_one (hFc.comp hγc).continuousOn
                (show f x' y' ∈ Set.Icc _ _ from ⟨by simpa [γ] using hlt.le, by simpa [γ] using hfd⟩)
              have hq1 : s ≤ (γ τ).1 := by
                show s ≤ x + τ * (x₂ - x); nlinarith [hτ.1, hτ.2]
              have hq2 : (γ τ).1 ≤ x₂ := by
                show x + τ * (x₂ - x) ≤ x₂; nlinarith [hτ.1, hτ.2]
              have hqT : (γ τ).1 ∈ T := by
                rcases eq_or_lt_of_le hq1 with h | h
                · rw [← h]; exact hsT
                · exact hR _ h hq2
              have hfq : f (γ τ).1 (γ τ).2 = f x' y' := hτv
              have h1 := (hF2 (f x' y') x' (γ τ).1 y' (γ τ).2 (by linarith) rfl hfq).1
              have h2 := hqT (γ τ).2 (by rw [hfq]; exact hfd)
              linarith
            have hiii : ∃ Y, f s Y ≤ d := by
              by_contra hno; push_neg at hno
              obtain ⟨x', -, hx's, -, y', hfd, -⟩ := hbad 1 one_pos
              let γ : ℝ → ℝ × ℝ := fun τ => (x' + τ * (s - x'), y' + τ * (0 - y'))
              have hγc : Continuous γ := by fun_prop
              obtain ⟨τ, hτ, hτv⟩ := intermediate_value_Icc zero_le_one (hFc.comp hγc).continuousOn
                (show d ∈ Set.Icc _ _ from ⟨by simpa [γ] using hfd, by simpa [γ] using (hno 0).le⟩)
              have hq1 : (γ τ).1 ≤ s := by
                show x' + τ * (s - x') ≤ s; nlinarith [hτ.1, hτ.2]
              have hfq : f (γ τ).1 (γ τ).2 = d := hτv
              obtain ⟨Y, hY⟩ := hconn d (γ τ).1 x₂ (γ τ).2 y₂ hfq rfl ⟨hq1, hs2⟩
              exact absurd hY (ne_of_gt (hno Y))
            have hiv : ∀ Y, e ≤ g s Y := by
              intro Y; by_contra hlt; push_neg at hlt
              have hfY : f s (Y - 1) < f s Y := hfm s (by linarith)
              have hev : ∀ᶠ x in nhds s, g x Y < e ∧ f s (Y-1) < f x Y :=
                ((hgx Y).continuousAt.eventually (gt_mem_nhds hlt)).and
                  ((hfx Y).continuousAt.eventually (lt_mem_nhds hfY))
              obtain ⟨δ, hδ, hδb⟩ := Metric.eventually_nhds_iff.mp hev
              obtain ⟨x', hx'1, hx's, -, y', hfd, hge⟩ := hbad δ hδ
              have hd' : dist x' s < δ := by rw [Real.dist_eq, abs_lt]; constructor <;> linarith
              obtain ⟨h1, h2⟩ := hδb hd'
              have h3 := hii x' y' hx's hfd hge s (Y-1) le_rfl hs2
              have hyY : y' < Y := (hfm x').lt_iff_lt.mp (show f x' y' < f x' Y by linarith)
              have := hgm x' hyY
              simp only at this
              linarith
            obtain ⟨Y, hY⟩ := hiii
            have h2 := hiv (Y - 1)
            have h3 := hsT Y hY
            have h4 : g s (Y-1) < g s Y := hgm s (by linarith)
            linarith
          intro x₁ y₁ x₂ y₂ h12 hle
          refine ⟨hweak x₁ y₁ x₂ y₂ h12 hle, ?_, ?_⟩
          · intro hlt
            have hev : ∀ᶠ y in nhdsWithin y₂ (Set.Iio y₂), f x₁ y₁ < f x₂ y :=
              Filter.Eventually.filter_mono nhdsWithin_le_nhds ((hfy x₂).continuousAt.eventually (lt_mem_nhds hlt))
            obtain ⟨y, hy, hy2⟩ := (hev.and self_mem_nhdsWithin).exists
            have h1 := hweak x₁ y₁ x₂ y h12 hy.le
            have h2 : g x₂ y < g x₂ y₂ := hgm x₂ hy2
            linarith
          · intro hs
            have hev : ∀ᶠ x in nhdsWithin x₁ (Set.Ioi x₁), (∃ y', |y' - y₁| < 1 ∧ f x y' = f x₁ y₁) ∧ x < x₂ :=
              (Filter.Eventually.filter_mono nhdsWithin_le_nhds (hloc x₁ y₁ 1 one_pos)).and (Filter.Eventually.filter_mono nhdsWithin_le_nhds (gt_mem_nhds h12))
            obtain ⟨x, ⟨⟨y', -, hfy'⟩, hx2⟩, hx1⟩ := (hev.and self_mem_nhdsWithin).exists
            have h1 := (hF2 (f x₁ y₁) x₁ x y₁ y' hx1 rfl hfy').2 hs
            have h2 := hweak x y' x₂ y₂ hx2 (by rw [hfy']; exact hle)
            linarith
        -- the global comparison along indifference curves (x'' < x')
        have hglob : ∀ (strict : Bool), (if strict then StrictSpenceMirrlees U else SpenceMirrlees U) →
            ∀ x'' y'' x' y' t'' t' : ℝ, x'' < x' → t'' < t' →
            U x'' y'' t'' ≤ U x' y' t'' →
            (if strict then U x'' y'' t' < U x' y' t' else U x'' y'' t' ≤ U x' y' t') ∧
            (U x'' y'' t'' < U x' y' t'' → U x'' y'' t' < U x' y' t') := by
          intro strict hSM x'' y'' x' y' t'' t' hx ht hle
          have hSMw : SpenceMirrlees U := by
            cases strict
            · simpa using hSM
            · exact fun x y => ((by simpa using hSM : StrictSpenceMirrlees U) x y).monotone
          have hSMs : strict = true → StrictSpenceMirrlees U := by
            intro h; subst h; simpa using hSM
          have hF3d : Differentiable ℝ (fun p : (ℝ × ℝ) × ℝ => U p.1.1 p.1.2 p.2) :=
            hF1.differentiable (by norm_num)
          have hUy : ∀ x y t, HasDerivAt (fun b => U x b t) (deriv (fun b => U x b t) y) y := by
            intro x y t
            have := (hDF ((x, y), t)).comp_hasDerivAt y
              (((hasDerivAt_const y x).prodMk (hasDerivAt_id y)).prodMk (hasDerivAt_const y t))
            exact this.differentiableAt.hasDerivAt
          have hUx : ∀ x y t, HasDerivAt (fun a => U a y t) (deriv (fun a => U a y t) x) x := by
            intro x y t
            have := (hDF ((x, y), t)).comp_hasDerivAt x
              (((hasDerivAt_id x).prodMk (hasDerivAt_const x y)).prodMk (hasDerivAt_const x t))
            exact this.differentiableAt.hasDerivAt
          have hLL : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → (∀ x y t, 0 < σ * deriv (fun b => U x b t) y) →
              ∀ t x y, ∃ L : ℝ × ℝ →L[ℝ] ℝ,
              HasFDerivAt (fun p : ℝ × ℝ => U p.1 (σ * p.2) t) L (x, y) ∧ 0 < L (0,1) ∧
              L (1,0) / L (0,1) = marginalRatio U x (σ * y) t := by
            intro σ hσ hpos t x y
            have hdiff : DifferentiableAt ℝ (fun p : ℝ × ℝ => U p.1 (σ * p.2) t) (x, y) := by
              have hm : DifferentiableAt ℝ (fun p : ℝ × ℝ => (((p.1, σ * p.2), t) : (ℝ × ℝ) × ℝ)) (x, y) := by
                fun_prop
              exact (hF3d _).comp (x, y) hm
            have hL := hdiff.hasFDerivAt
            set L := fderiv ℝ (fun p : ℝ × ℝ => U p.1 (σ * p.2) t) (x, y)
            have h01 : HasDerivAt (fun b => U x (σ * b) t) (L (0,1)) y :=
              hL.comp_hasDerivAt y ((hasDerivAt_const y x).prodMk (hasDerivAt_id y))
            have h01' : HasDerivAt (fun b => U x (σ * b) t) (deriv (fun b => U x b t) (σ * y) * (σ * 1)) y :=
              (hUy x (σ * y) t).comp y ((hasDerivAt_id' y).const_mul σ)
            have h10 : HasDerivAt (fun a => U a (σ * y) t) (L (1,0)) x := by
              have := hL.comp_hasDerivAt x ((hasDerivAt_id' x).prodMk (hasDerivAt_const x y))
              exact this
            have e01 := h01.unique h01'
            have e10 := h10.unique (hUx x (σ * y) t)
            have hp := hpos x (σ * y) t
            refine ⟨L, hL, ?_, ?_⟩
            · rw [e01, mul_one, mul_comm]; exact hp
            · unfold marginalRatio
              rw [e01, e10, mul_one]
              congr 1
              rcases hσ with rfl | rfl
              · rw [abs_of_pos (by linarith)]; ring
              · rw [abs_of_neg (by linarith)]; ring
          have hpc' : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ c, {p : ℝ × ℝ | U p.1 (σ * p.2) t'' = c} = ∅ ∨
              IsPathConnected {p : ℝ × ℝ | U p.1 (σ * p.2) t'' = c} := by
            intro σ hσ c
            have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
            have he : {p : ℝ × ℝ | U p.1 (σ * p.2) t'' = c} =
                (fun p : ℝ × ℝ => (p.1, σ * p.2)) '' {p : ℝ × ℝ | U p.1 p.2 t'' = c} := by
              ext ⟨a, b⟩
              simp only [Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
              constructor
              · intro h; exact ⟨a, σ * b, h, rfl, by rw [← mul_assoc, hσσ, one_mul]⟩
              · rintro ⟨a', b', h, rfl, rfl⟩; rw [← mul_assoc, hσσ, one_mul]; exact h
            rw [he]
            rcases hreg.2 t'' c with h | h
            · left; rw [h, Set.image_empty]
            · right; exact h.image (by fun_prop)
          obtain ⟨σ, hσ, hpos⟩ : ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∀ x y t, 0 < σ * deriv (fun b => U x b t) y := by
            rcases hsign with h | h
            · exact ⟨1, Or.inl rfl, fun x y t => by simpa using h x y t⟩
            · exact ⟨-1, Or.inr rfl, fun x y t => by have := h x y t; linarith⟩
          have hσσ : σ * σ = 1 := by rcases hσ with rfl | rfl <;> norm_num
          have hc := core (strict = true) (fun x y => U x (σ * y) t'') (fun x y => U x (σ * y) t') (by
            intro x y
            obtain ⟨L, hL, hL0, hLr⟩ := hLL σ hσ hpos t'' x y
            obtain ⟨L', hL', hL0', hLr'⟩ := hLL σ hσ hpos t' x y
            refine ⟨L, L', hL, hL', hL0, hL0', ?_, ?_⟩
            · rw [hLr, hLr']; exact hSMw x (σ * y) ht.le
            · intro hs; rw [hLr, hLr']; exact hSMs hs x (σ * y) ht) (hpc' σ hσ)
            x'' (σ * y'') x' (σ * y') hx (by simp only [← mul_assoc, hσσ, one_mul]; exact hle)
          simp only [← mul_assoc, hσσ, one_mul] at hc
          obtain ⟨h1, h2, h3⟩ := hc
          refine ⟨?_, h2⟩
          cases strict
          · simpa using h1
          · simpa using h3 rfl
        have hsuffW : SpenceMirrlees U → LexSingleCrossing U := by
          intro hSM p' p'' hp t' t'' ht
          simp only
          rcases Prod.Lex.lt_iff.mp hp with h1 | ⟨h1, h1'⟩
          · have := hglob false (by simpa using hSM) (ofLex p'').1 (ofLex p'').2 (ofLex p').1 (ofLex p').2
              t'' t' h1 ht
            refine ⟨fun hlt => (this hlt.le).2 hlt, fun hle => by simpa using (this hle).1⟩
          · rw [h1]
            rcases hmono with hm | hm
            · exact ⟨fun _ => hm _ _ h1', fun _ => (hm _ _ h1').le⟩
            · have := hm (ofLex p').1 t'' h1'
              exact ⟨fun h => absurd h (lt_asymm this), fun h => absurd h (not_le.mpr this)⟩
        have hsuffS : StrictSpenceMirrlees U → LexStrictSingleCrossing U := by
          intro hSM p' p'' hp t' t'' ht hle
          simp only at hle ⊢
          rcases Prod.Lex.lt_iff.mp hp with h1 | ⟨h1, h1'⟩
          · have := hglob true (by simpa using hSM) (ofLex p'').1 (ofLex p'').2 (ofLex p').1 (ofLex p').2
              t'' t' h1 ht hle
            simpa using this.1
          · rw [h1] at hle ⊢
            rcases hmono with hm | hm
            · exact hm _ _ h1'
            · exact absurd hle (not_le.mpr (hm _ _ h1'))
        exact ⟨⟨hnec, hsuffW⟩, hsuffS, hcub⟩
