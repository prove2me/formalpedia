-- Prove2me | solution 1 for GlobalTheory.LeadingMinors.coeff_prod_leading_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:17:54.128973+00:00
-- url     : https://prove2.me/submissions/d2af8371-d417-4745-8161-414dd6ac6ba4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Theorems.Thm_GlobalTheory_LeadingMinors_isHomogeneous_det_X
import Theorems.Thm_GlobalTheory_LeadingMinors_det_X_mem_supported
import Theorems.Thm_GlobalTheory_LeadingMinors_killCompl_det_X

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.LeadingMinors
open MvPowerSeries
namespace GlobalTheory.LeadingMinors
namespace _root_.GlobalTheory.LeadingMinors
theorem _root_.solution : ∀ (k : Type) [CommRing k] (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → P.coeff al = 1 ∧ P.IsHomogeneous al.degree ∧ al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) ∧ ∀ mo ∈ P.support, ∀ l b, mo (l, b) ≠ 0 → ∃ i, col l.1 i = b := by
  intro k _ T _ _ r n col m hcol P al hP hal
  have hf : Function.Injective
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) :=
    fun a b h => congrArg Prod.fst h
  have hblock : ∀ τ (s : Fin (r τ)), MvPolynomial.killCompl hf
      (Matrix.of fun a i : Fin (s.val + 1) =>
        (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det =
      MvPolynomial.monomial
        (∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1)
        1 := fun τ s =>
    _root_.GlobalTheory.LeadingMinors.killCompl_det_X hf _ (fun a => ⟨τ, Fin.castLE s.isLt a⟩)
      (fun _ => rfl) (by
        rintro a i hai ⟨l, hl⟩
        simp only [Prod.mk.injEq] at hl
        obtain ⟨rfl, h⟩ := hl
        exact hai (Fin.castLE_injective _ (hcol τ h)))
  set B : (Σ τ : T, Fin (r τ)) →₀ ℕ := ∑ τ, ∑ s : Fin (r τ), m τ s •
    ∑ a : Fin (s.val + 1), Finsupp.single (⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)) 1
    with hBdef
  have hkill : MvPolynomial.killCompl hf P = MvPolynomial.monomial B 1 := by
    rw [hP, hBdef, map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [map_prod, MvPolynomial.monomial_sum_one]
    refine Finset.prod_congr rfl fun s _ => ?_
    rw [map_pow, hblock, MvPolynomial.monomial_pow, one_pow]
  have hmap : Finsupp.mapDomain
      (fun l : Σ τ : T, Fin (r τ) => ((l, col l.1 l.2) : (Σ τ : T, Fin (r τ)) × Fin n)) B = al := by
    rw [hal, hBdef]
    simp [Finsupp.mapDomain_finset_sum, Finsupp.mapDomain_smul, Finsupp.mapDomain_single]
  have hdeg : al.degree = ∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1) := by
    rw [hal]
    simp [map_sum, Finsupp.degree_single]
  have hhom : P.IsHomogeneous (∑ τ, ∑ s : Fin (r τ), m τ s * (s.val + 1)) := by
    rw [hP]
    refine MvPolynomial.IsHomogeneous.prod _ _ _ fun τ _ =>
      MvPolynomial.IsHomogeneous.prod _ _ _ fun s _ => ?_
    have h := (_root_.GlobalTheory.LeadingMinors.isHomogeneous_det_X (k := k)
      (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
        col τ (Fin.castLE s.isLt i)))).pow (m τ s)
    rw [Fintype.card_fin] at h
    rwa [mul_comm] at h
  have hsupp : P ∈ MvPolynomial.supported k
      {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2} := by
    rw [hP]
    exact Subalgebra.prod_mem _ fun τ _ => Subalgebra.prod_mem _ fun s _ =>
      Subalgebra.pow_mem _ (_root_.GlobalTheory.LeadingMinors.det_X_mem_supported
        (fun a i : Fin (s.val + 1) => ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)),
          col τ (Fin.castLE s.isLt i)))
        {x : (Σ τ : T, Fin (r τ)) × Fin n | ∃ i, col x.1.1 i = x.2}
        fun a i => ⟨Fin.castLE s.isLt i, rfl⟩) _
  refine ⟨?_, by rw [hdeg]; exact hhom, hdeg, fun mo hmo l b hlb => ?_⟩
  · rw [← hmap, ← MvPolynomial.coeff_killCompl hf, hkill, MvPolynomial.coeff_monomial, if_pos rfl]
  · have hv : (l, b) ∈ P.vars :=
      (MvPolynomial.mem_vars _).2 ⟨mo, hmo, Finsupp.mem_support_iff.2 hlb⟩
    exact MvPolynomial.mem_supported.1 hsupp hv
end _root_.GlobalTheory.LeadingMinors
end GlobalTheory.LeadingMinors
