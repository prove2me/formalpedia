-- Prove2me | solution 1 for HorizontalPadicL.eigenform_period_lattice_uniformly_integral_v2
-- status  : ACCEPTED   (prove)
-- author  : @davidloeffler
-- created : 2026-09-25T11:42:16.513952+00:00
-- url     : https://prove2.me/submissions/b3e61adc-82bd-4a42-9154-cfdab725741f

import Definitions.Def_KN_SeededThetaConstructionV2B
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.RingTheory.Localization.Integral
import Mathlib.RingTheory.Valuation.Integral

set_option autoImplicit false
noncomputable section

open HorizontalPadicL

theorem _root_.solution
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (_hnew : IsNewEigenform f)
    (ιp : MTT.Qbar →+* ℂ_[p]) (P : MTT.Periods k ι f.form) :
    Nonempty (IntegralPeriodScale f ιp P) := by
  classical
  let L : Submodule ℤ MTT.Qbar :=
    Submodule.span ℤ {v : MTT.Qbar | ∃ s j r,
      j ≤ k - 2 ∧ v = P.value s j r}
  have hLfg : L.FG := P.lattice_fg
  obtain ⟨n, g, hg⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp hLfg

  -- Algebraic numbers are algebraic over `ℤ` as well as over `ℚ`, so a
  -- finite family admits one common integral denominator.
  letI : Algebra.IsAlgebraic ℚ MTT.Qbar :=
    AlgebraicClosure.isAlgebraic ℚ
  letI : Algebra.IsAlgebraic ℤ MTT.Qbar :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)
      (C := MTT.Qbar)).2 inferInstance
  obtain ⟨d, hd, hdint⟩ :=
    Algebra.IsAlgebraic.exists_integral_multiples ℤ (Finset.univ.image g)

  have hgen (i : Fin n) : IsIntegral ℤ (d • g i) :=
    hdint (g i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  have hall {x : MTT.Qbar} (hx : x ∈ L) : IsIntegral ℤ (d • x) := by
    rw [← hg] at hx
    refine Submodule.span_induction
      (p := fun x _ => IsIntegral ℤ (d • x)) ?_ ?_ ?_ ?_ hx
    · rintro x ⟨i, rfl⟩
      exact hgen i
    · simpa using (isIntegral_zero : IsIntegral ℤ (0 : MTT.Qbar))
    · intro x y hx hy hix hiy
      simpa [smul_add] using hix.add hiy
    · intro a x hx hix
      convert hix.zsmul a using 1 <;> simp <;> ring

  refine ⟨{
    scale := (d : MTT.Qbar)
    scale_ne_zero := by exact_mod_cast hd
    integral_value := ?_ }⟩
  intro s j r hj
  have hmem : P.value s j r ∈ L :=
    Submodule.subset_span ⟨s, j, r, hj, rfl⟩
  have hint : IsIntegral ℤ ((d : MTT.Qbar) * P.value s j r) := by
    simpa [smul_eq_mul] using hall hmem

  -- An algebraic integer remains integral after embedding in `ℂ_[p]`, and
  -- the integral closure lies in the valuation ring `𝓞_ℂ_[p]`.
  have hint' :
      IsIntegral ℤ (ιp ((d : MTT.Qbar) * P.value s j r)) := by
    change (algebraMap ℤ ℂ_[p]).IsIntegralElem
      (ιp ((d : MTT.Qbar) * P.value s j r))
    rw [← show ιp.comp (algebraMap ℤ MTT.Qbar) =
        algebraMap ℤ ℂ_[p] by
      ext z
      simp]
    exact RingHom.IsIntegralElem.map hint ιp
  have hintO : IsIntegral 𝓞_ℂ_[p]
      (ιp ((d : MTT.Qbar) * P.value s j r)) := hint'.tower_top
  change Valued.v (ιp ((d : MTT.Qbar) * P.value s j r)) ≤ 1
  exact (PadicComplexInt.integers (p := p)).isIntegral_iff_v_le_one.mp hintO
