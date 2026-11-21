-- Prove2me | solution 1 for MasulloRH.off_line_zero_has_four_distinct_symmetries
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T04:01:48.629149+00:00
-- url     : https://prove2.me/submissions/4580683d-31a5-4e8b-a88a-223ae7f904e3

-- Four distinct off-line strip zeros at the same absolute ordinate.
import Theorems.Thm_ZetaKernel_rect6_riemannZeta_ne_zero_of_abs_im_le_six
import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib
open MasulloRH Complex

theorem solution (z : ZetaZerosInTraceStrip (1/2)) (hz : z.val.re ≠ 1/2) :
    ∃ S : Finset {u : ZetaZerosInTraceStrip (1/2) // u.val.re ≠ 1/2},
      S.card = 4 ∧ ∀ u ∈ S, |u.val.val.im| = |z.val.im| := by
  classical
  let A := {u : ZetaZerosInTraceStrip (1/2) // u.val.re ≠ 1/2}
  have hx := z.prop.2.1
  have hy := z.prop.2.2.1
  have hi : z.val.im ≠ 0 := by
    intro h
    exact ZetaKernel.rect6_riemannZeta_ne_zero_of_abs_im_le_six hx hy (by simp [h]) z.prop.1
  let conjZ (a : A) : A := ⟨⟨starRingEnd ℂ a.val.val,by
    refine ⟨?_,a.val.prop.2⟩
    simpa only [riemannZeta_conj,a.val.prop.1,map_zero]⟩,a.prop⟩
  have hfun : riemannZeta (1-z.val) = 0 := by
    rw [riemannZeta_one_sub, z.prop.1,mul_zero]
    · intro n h
      have := congrArg Complex.re h
      simp only [Complex.neg_re,Complex.natCast_re] at this
      linarith [Nat.cast_nonneg (α:=ℝ) n]
    · intro h
      have := congrArg Complex.re h
      simp only [Complex.one_re] at this
      linarith
  let a : A := ⟨z,hz⟩
  let b : A := ⟨⟨1-z.val,by
    refine ⟨hfun,?_,?_,?_⟩ <;> simp only [Complex.sub_re,Complex.one_re]
    · linarith
    · linarith
    · exact abs_lt.mpr ⟨by linarith,by linarith⟩⟩,by
      simp only [Complex.sub_re,Complex.one_re]; intro h; apply hz; linarith⟩
  let g : Bool × Bool → A := fun i => match i with
    | (false,false) => a
    | (false,true) => conjZ a
    | (true,false) => b
    | (true,true) => conjZ b
  have hg : Function.Injective g := by
    rintro ⟨i,j⟩ ⟨k,l⟩ h
    have hr := congrArg (fun v : A => v.val.val.re) h
    have ht := congrArg (fun v : A => v.val.val.im) h
    cases i <;> cases j <;> cases k <;> cases l <;> first
      | rfl
      | exfalso
        simp only [g,a,b,conjZ,Complex.conj_re,Complex.conj_im,Complex.sub_re,Complex.one_re,
          Complex.sub_im,Complex.one_im,zero_sub,neg_neg] at hr ht
        first | exact hz (by linarith only [hr]) | exact hi (by linarith only [ht])
  refine ⟨Finset.univ.map ⟨g,hg⟩,by simp,?_⟩
  intro u hu
  obtain ⟨⟨i,j⟩,_,rfl⟩ := Finset.mem_map.mp hu
  cases i <;> cases j <;> simp [g,a,b,conjZ]
