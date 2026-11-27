-- Prove2me | solution 1 for GlobalTheory.minors_disjoint_columns_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:26.768817+00:00
-- url     : https://prove2.me/submissions/d6c8f07a-69e1-4517-8959-3e05604d291f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MinorsDisjointColumnsHarmonic
import Theorems.Thm_GlobalTheory_minorHarm_pderiv_eq_zero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
namespace GlobalTheory
open MvPowerSeries in
private theorem pderiv_mem_supported' {σ k : Type*} [CommRing k] {S : Set σ}
    {p : MvPolynomial σ k} (hp : p ∈ MvPolynomial.supported k S) (w : σ) :
    MvPolynomial.pderiv w p ∈ MvPolynomial.supported k S := by
  classical
  rw [MvPolynomial.supported_eq_adjoin_X] at hp ⊢
  induction hp using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨s, hs, rfl⟩ := hx
    rw [MvPolynomial.pderiv_X]
    by_cases h : w = s
    · subst h; simp only [Pi.single_eq_same]; exact Subalgebra.one_mem _
    · rw [Pi.single_eq_of_ne' h]; exact Subalgebra.zero_mem _
  | algebraMap r =>
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.pderiv_C]; exact Subalgebra.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Subalgebra.add_mem _ hx hy
  | mul x y hx' hy' hx hy =>
    rw [MvPolynomial.pderiv_mul]
    exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ hx hy') (Subalgebra.mul_mem _ hx' hy)
end GlobalTheory
end

set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open MvPowerSeries
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution :
    ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ) (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → ∀ τ τ' : T, (∀ i i', col τ i ≠ col τ' i') → ∀ (i : Fin (r τ)) (i' : Fin (r τ')), ∑ b : Fin n, MvPolynomial.pderiv ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) (MvPolynomial.pderiv ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), b) P) = 0 := by
  intro k _ T _ _ r n col m P hP τ τ' hdisj i i'
  let S : Set ((Σ τ : T, Fin (r τ)) × Fin n) := {x | ∃ c, col x.1.1 c = x.2}
  have hPS : P ∈ MvPolynomial.supported k S := by
    rw [hP]
    refine Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun s _ => ?_
    refine Subalgebra.pow_mem _ ?_ _
    rw [Matrix.det_apply]
    refine Subalgebra.sum_mem _ fun π _ => ?_
    rw [Units.smul_def]
    refine Subalgebra.zsmul_mem _ (Subalgebra.prod_mem _ fun a _ => ?_) _
    rw [Matrix.of_apply, MvPolynomial.supported_eq_adjoin_X]
    exact Algebra.subset_adjoin ⟨_, ⟨_, rfl⟩, rfl⟩
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : ∃ c, col τ c = b
  · obtain ⟨c, rfl⟩ := hb
    have hnot : ((⟨τ', i'⟩ : Σ τ : T, Fin (r τ)), col τ c) ∉ S := by
      rintro ⟨c', hc'⟩
      exact hdisj c c' hc'.symm
    rw [_root_.GlobalTheory.minorHarm_pderiv_eq_zero hPS hnot, map_zero]
  · have hnot : ((⟨τ, i⟩ : Σ τ : T, Fin (r τ)), b) ∉ S := hb
    exact _root_.GlobalTheory.minorHarm_pderiv_eq_zero
      (pderiv_mem_supported' hPS _) hnot
end _root_.GlobalTheory
end GlobalTheory
