-- Prove2me | solution 1 for GlobalTheory.sum_prod_nabVal_leading_minors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:42.782807+00:00
-- url     : https://prove2.me/submissions/ff52b009-faff-4b44-96e4-e34dc7350d25

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfCongrJet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdConstantCoeffDmonOfCols
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_CoeffProdLeadingMinors
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SumProdNabValLeadingMinors
import Theorems.Thm_GlobalTheory_CrudeValue_constantCoeff_expS
import Theorems.Thm_GlobalTheory_CrudeValue_constantCoeff_hL
import Theorems.Thm_GlobalTheory_CrudeValue_nabVal_monomial
import Theorems.Thm_GlobalTheory_LeadingMinors_coeff_prod_leading_minors
import Theorems.Thm_GlobalTheory_SymbolCols_coeff_mul_congr
import Theorems.Thm_GlobalTheory_SymbolCols_sum_degree_colM
import Theorems.Thm_GlobalTheory_constantCoeff_DmonOf_congr_jet
import Theorems.Thm_GlobalTheory_sum_prod_constantCoeff_dmonOf_cols


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open CrudeValue SymbolCols
namespace GlobalTheory
theorem _root_.solution : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k] (B : FB R d O) (h : PS k 2 d), constantCoeff h = 0 → ∀ (w0 : O) (q : ℕ) (T : Type) [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ) (col : ∀ τ, Fin (r τ) → Fin n) (m : ∀ τ, Fin (r τ) → ℕ), (∀ τ, Function.Injective (col τ)) → ∀ (P : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k) (al : (Σ τ : T, Fin (r τ)) × Fin n →₀ ℕ), P = (∏ τ, ∏ s : Fin (r τ), (Matrix.of fun a i : Fin (s.val + 1) => (MvPolynomial.X ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt i)) : MvPolynomial ((Σ τ : T, Fin (r τ)) × Fin n) k)).det ^ m τ s) → al = ∑ τ, ∑ s : Fin (r τ), m τ s • ∑ a : Fin (s.val + 1), Finsupp.single ((⟨τ, Fin.castLE s.isLt a⟩ : Σ τ : T, Fin (r τ)), col τ (Fin.castLE s.isLt a)) 1 → ∀ (u : (Σ τ : T, Fin (r τ)) → Fin d → k) (lam : Fin n → (Σ τ : T, Fin (r τ)) → Fin d → k), (∀ b l l', (∃ i, col l.1 i = b) → (∃ i, col l'.1 i = b) → ∑ i, lam b l i * u l' i = if l = l' then 1 else 0) → ∀ (c : Fin n → k) (f : Fin n → PS k 1 d), (∀ b (mo : Fin 1 × Fin d →₀ ℕ), mo.degree ≤ al.degree → coeff mo (f b) = c b * coeff mo (∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b))) → ∑ mo ∈ P.support, P.coeff mo * ∏ b, B.nabVal k h w0 q (f b) u (MvPolynomial.monomial (colM mo b) 1) = (∏ b, c b) * ∏ p, ((al p).factorial : k) := by
  intro R _ d O _ _ k _ _ _ B h hh w0 q T _ _ r n col m hcol P al hP hal u lam hpair c f hf
  obtain ⟨h1, hhom, -, hsupp⟩ :=
    LeadingMinors.coeff_prod_leading_minors k T r n col m hcol P al hP hal
  rcases subsingleton_or_nontrivial k with hk | hk
  · exact Subsingleton.elim _ _
  have halP : al ∈ P.support := by
    rw [MvPolynomial.mem_support_iff, h1]
    exact one_ne_zero
  set E : PS k 1 d := FB.expS k ((q : k) • B.hL k h w0) with hE
  have hE1 : constantCoeff E = 1 := constantCoeff_expS _ (by
    rw [smul_eq_C_mul, map_mul, constantCoeff_hL B h hh w0, mul_zero])
  set g : Fin n → PS k 1 d := fun b =>
    ∏ l, (∑ i, C (lam b l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al (l, b) with hg
  have key := sum_prod_constantCoeff_dmonOf_cols R k (algebraMap R k) d B.G _ n u lam (fun _ => 1)
    al P g (fun b => C (c b) * E) hhom
    (fun b l l' hl ⟨mo, hmo, hl'⟩ => hpair b l l' (hsupp al halP l b hl) (hsupp mo hmo l' b hl'))
    (fun b mo _ => rfl)
  have hdeg : ∀ mo ∈ P.support, mo.degree = al.degree := fun mo hmo => by
    have := hhom (MvPolynomial.mem_support_iff.1 hmo)
    rw [← this, Finsupp.degree_eq_weight_one]
    rfl
  refine Eq.trans (Finset.sum_congr rfl fun mo hmo => ?_) (key.trans ?_)
  · congr 1
    refine Finset.prod_congr rfl fun b _ => ?_
    have hle : (colM mo b).degree ≤ al.degree := by
      rw [← hdeg mo hmo, ← sum_degree_colM]
      exact Finset.single_le_sum (f := fun b => (colM mo b).degree) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ b)
    rw [nabVal_monomial, ← hE, ← mul_assoc, mul_comm (g b)]
    refine constantCoeff_DmonOf_congr_jet k d _ _ u (colM mo b) _ _ fun mo' hm => ?_
    refine coeff_mul_congr al.degree _ _ E (fun mo'' hm' => ?_) mo' (hm.trans hle)
    rw [coeff_C_mul]
    exact hf b mo'' hm'
  · simp only [h1, one_mul, one_pow, mul_one, map_mul, constantCoeff_C, hE1]
    rw [Finset.prod_mul_distrib, mul_comm, Fintype.prod_prod_type_right]
end GlobalTheory
