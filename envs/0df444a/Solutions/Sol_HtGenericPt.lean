-- Prove2me | solution 1 for HtGenericPt
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:48:49.165614+00:00
-- url     : https://prove2.me/submissions/acd66747-1380-4cbc-8527-dec3260b6948

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GenericPointHeight_GenericPointStatements_GenericPointLemmas_GenericPointWeights_Wx
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussHeights_GenericPointHeight_GenericPointStatements_GenericPointTheorem_HtGenericPt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
theorem _root_.solution {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] {WT : Type} [AddCommGroup WT] {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : ReciprocityTheory.ChartRestriction.G.T0.Data K ι Ω WT A) : ReciprocityTheory.ChartRestriction.G.T0.LeafSt.exists_generic 𝒜 d := by
  classical
  intro hd h
  refine ⟨?_, ⟨hd.a4.choose, hd.a4.choose_spec.1⟩⟩
  have hφ : ∀ c, ∃ φ : Module.Dual K (A c), φ (d.w (d.jc c) c) ≠ 0 := by
    intro c
    by_contra hcon
    push_neg at hcon
    exact hd.w_base c ((Module.forall_dual_apply_eq_zero_iff K _).mp hcon)
  choose φ hφ using hφ
  let P : ι → MvPolynomial (Fin (d.N + 1)) K := fun c =>
    ∑ j, MvPolynomial.C (φ c (d.w j c)) * MvPolynomial.X j
  have hev : ∀ (x : Fin (d.N + 1) → K) c, MvPolynomial.eval x (P c) = φ c (d.wx x c) := by
    intro x c
    simp only [P, map_sum, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
      ReciprocityTheory.ChartRestriction.G.T0.Data.wx, Finset.sum_apply, Pi.smul_apply, map_smul, smul_eq_mul]
    exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  have hP : ∀ c, P c ≠ 0 := by
    intro c hc
    apply hφ c
    have := congrArg (MvPolynomial.coeff (Finsupp.single (d.jc c) 1)) hc
    simpa [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X',
      Finsupp.single_eq_single_iff] using this
  have hprod : (∏ c, P c) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun c _ => hP c)
  haveI : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  by_contra hne
  push_neg at hne
  apply hprod
  apply MvPolynomial.funext
  intro x
  obtain ⟨c, hc⟩ := hne x
  rw [map_prod, map_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ c) (by rw [hev, hc, map_zero])
