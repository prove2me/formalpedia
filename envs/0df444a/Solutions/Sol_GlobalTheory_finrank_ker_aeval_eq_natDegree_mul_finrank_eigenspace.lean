-- Prove2me | solution 1 for GlobalTheory.finrank_ker_aeval_eq_natDegree_mul_finrank_eigenspace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:12:52.955782+00:00
-- url     : https://prove2.me/submissions/9ad84bf6-7ed6-461f-8f55-4a83797d9107

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankKerAevalEqNatDegreeMulFinrankEigenspaceAl
import Theorems.Thm_GlobalTheory_eigDim_ker_map
import Theorems.Thm_GlobalTheory_eigDim_ker_aeval_map
import Theorems.Thm_GlobalTheory_eigDim_ker_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (F : Type) [Field F] [Finite F] (ι : Type) [Fintype ι] [DecidableEq ι] (M : Matrix ι ι F) (f : F[X]) (y : AlgebraicClosure F), Irreducible f → aeval y f = 0 → Module.finrank F (LinearMap.ker (aeval (Matrix.toLin' M) f)) = f.natDegree * Module.finrank (AlgebraicClosure F) (Module.End.eigenspace (Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)))) y) := by
  intro F _ _ ι _ _ M f y hf hy
  classical
  rw [← eigDim_ker_aeval_map (algebraMap F (AlgebraicClosure F)) M f]
  set g := f.map (algebraMap F (AlgebraicClosure F)) with hg
  set T := Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F))) with hT
  have hsep : g.Separable := (PerfectField.separable_of_irreducible hf).map
  have hne : g ≠ 0 := Polynomial.map_ne_zero hf.ne_zero
  have hnd := Polynomial.nodup_roots hsep
  have hcard : Multiset.card g.roots = g.natDegree :=
    (IsAlgClosed.splits g).natDegree_eq_card_roots.symm
  have hfac := Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C hcard
  have hprod : (g.roots.map fun a => X - C a).prod = ∏ a ∈ g.roots.toFinset, (X - C a) := by
    rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnd]
  have hlc : g.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hne
  have hker : aeval T g = g.leadingCoeff • aeval T (∏ a ∈ g.roots.toFinset, (X - C a)) := by
    conv_lhs => rw [← hfac, hprod]
    rw [map_mul, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
  have hterm : ∀ a ∈ g.roots.toFinset, Module.finrank (AlgebraicClosure F) (LinearMap.ker (aeval T (X - C a))) =
      Module.finrank (AlgebraicClosure F) (Module.End.eigenspace T y) := by
    intro a ha
    have haroot : aeval a f = 0 := by
      have h0 := Polynomial.IsRoot.eq_zero ((Polynomial.mem_roots hne).mp (Multiset.mem_toFinset.mp ha))
      rwa [hg, Polynomial.eval_map_algebraMap] at h0
    have hmin : minpoly F a = minpoly F y := by
      rw [← minpoly.eq_of_irreducible hf haroot, ← minpoly.eq_of_irreducible hf hy]
    obtain ⟨σ, hσ⟩ := MulAction.mem_orbit_iff.mp ((Normal.minpoly_eq_iff_mem_orbit (AlgebraicClosure F)).mp hmin)
    rw [AlgEquiv.smul_def] at hσ
    have hmat : (M.map (algebraMap F (AlgebraicClosure F)) - y • (1 : Matrix ι ι (AlgebraicClosure F))).map (σ : AlgebraicClosure F →+* AlgebraicClosure F) = M.map (algebraMap F (AlgebraicClosure F)) - a • 1 := by
      ext i j
      by_cases hij : i = j <;> simp [hij, hσ]
    have e1 : aeval T (X - C a) = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - a • 1) := by
      rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, Algebra.algebraMap_eq_smul_one, hT,
        map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    have e2 : T - y • 1 = Matrix.toLin' (M.map (algebraMap F (AlgebraicClosure F)) - y • 1) := by
      rw [hT, map_sub, map_smul, Matrix.toLin'_one, Module.End.one_eq_id]
    rw [Module.End.eigenspace_def, e1, e2, ← hmat, eigDim_ker_map]
  rw [hker, LinearMap.ker_smul _ _ hlc, eigDim_ker_prod, Finset.sum_congr rfl hterm,
    Finset.sum_const, smul_eq_mul, Multiset.toFinset_card_of_nodup hnd, hcard, hg,
    Polynomial.natDegree_map]
end GlobalTheory
