-- Prove2me | solution 1 for GlobalTheory.constantCoeff_dmonOf_prod_linear
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T01:19:59.980143+00:00
-- url     : https://prove2.me/submissions/84091dad-411b-4706-ac6c-e94289a27ae0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_DofDApply
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_WickVanishing_GaugeBilinearTermEqNegDoubleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_DerivationMemPowOfMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ConstantCoeffDmonOfProdLinear
import Theorems.Thm_GlobalTheory_SymbolOne_word_value
import Theorems.Thm_GlobalTheory_SymbolOne_exists_word
import Theorems.Thm_GlobalTheory_SymbolOne_constantCoeff_dof_X
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dofD_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_C_mul
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_TB_GE_dof_sum


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory
open SymbolOne
namespace GlobalTheory
theorem _root_.solution :
    ∀ (R k : Type) [CommRing R] [CommRing k] (φ : R →+* k) (d : ℕ) (G : FGLaw R d) (ι : Type) [Fintype ι] [DecidableEq ι] (u lam : ι → Fin d → k) (α : ι → k) (al m : ι →₀ ℕ) (E : PS k 1 d), (∀ l l', al l ≠ 0 → m l' ≠ 0 → ∑ i, lam l i * u l' i = if l = l' then α l else 0) → m.degree ≤ al.degree → constantCoeff (DmonOf (G.mapF φ) u m ((∏ l, (∑ i, C (lam l i) * (X ((0 : Fin 1), i) : PS k 1 d)) ^ al l) * E)) = if m = al then (∏ l, ((al l).factorial : k) * α l ^ al l) * constantCoeff E else 0 := by
  intro R k _ _ φ d G ι _ _ u lam α al m E hpair hdeg
  obtain ⟨w, hw1, hw2⟩ := exists_word (fun l => Dof (G.mapF φ) (u l)) m (Finset.univ : Finset ι).toList
  have hc : ∀ l, w.count l = m l := fun l => by
    rw [hw1, List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp), one_mul]
  let π : PS k 1 d →ₐ[k] k :=
    { (constantCoeff : PS k 1 d →+* k) with commutes' := fun r => constantCoeff_C r }
  have hπ : ∀ f, π f = constantCoeff f := fun _ => rfl
  have hlen : w.length = ∑ l, m l := by
    rw [← Finset.sum_congr rfl fun l _ => hc l]
    have := Multiset.sum_count_eq_card (s := Finset.univ) (m := (w : Multiset ι)) (by simp)
    simpa using this.symm
  have key := word_value π (fun l => GE.dofD (G.mapF φ) (u l))
    (fun l => ∑ i, C (lam l i) * (X ((0 : Fin 1), i) : PS k 1 d)) (fun l => by simp [hπ]) α w al E
    (fun l l' hl hl' => by
      rw [hπ, GE.dofD_apply, GE.dof_sum, map_sum]
      simp only [GE.dof_C_mul, map_mul, constantCoeff_C, constantCoeff_dof_X]
      exact hpair l l' hl (by rw [← hc]; exact (List.count_pos_iff.2 hl').ne'))
    (by rw [hlen]; simpa [Finsupp.degree_eq_sum] using hdeg)
  simp only [GE.dofD_apply, hπ, hc] at key
  unfold DmonOf
  rw [hw2, key]
  simp only [Finsupp.ext_iff]
end GlobalTheory
