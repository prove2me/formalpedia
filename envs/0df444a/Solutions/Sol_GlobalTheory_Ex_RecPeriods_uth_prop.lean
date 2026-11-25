-- Prove2me | solution 1 for GlobalTheory.Ex.RecPeriods.uth_prop
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T07:51:46.392605+00:00
-- url     : https://prove2.me/submissions/40983764-5167-48f8-bfdf-9f53f5bf86f5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_MulqLawsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_DegenerationDataTorsionStructureAlgClosed
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsIsoOnG
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_uth_iso
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_txT_eq
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_exists_lift
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_exists_partner
import Theorems.Thm_GlobalTheory_Ex_RecPeriods_r_powRep
import Theorems.Thm_GlobalTheory_Ex_QStr_exists_lift


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex GlobalTheory.Ex.RecPeriods
variable {C : Type} [NormedField C] {N N' : NumD C} {n : ℕ} (μ : Match N N' n)
namespace GlobalTheory.Ex.RecPeriods
theorem _root_.solution [IsAlgClosed C] (hn : Odd n) (hN : ∀ b : N.A, ∃ γ : N.Gt, γ.b = b) {e : N.X ≃+ N'.X} (hB : μ.B e)
    (hT : μ.Term e) {I : NumB.Iso N.toNumB N'.toNumB} (hI : μ.OnB I) (j : ℕ) (p₁ : N.QT (n ^ j)) (p₁' : N'.QT (n ^ j))
    (h₁ : μ.r _ p₁ p₁') (he : p₁'.1.1.toAdd = e p₁.1.1.toAdd) (b : N.A) (hb : b ^ (n ^ j) ^ 2 = 1) :
    (N'.ψ (e p₁.1.1.toAdd) * mulq N'.θ N'.σ (n ^ j) p₁'.1.2.b * (I.lam * I.h p₁.1.2.b ^ (n ^ j) ^ 2) : Cˣ) *
      N'.uth (n ^ j) (I.φ b) p₁'.1.2.b =
    μ.c₀ * (N.ψ p₁.1.1.toAdd * mulq N.θ N.σ (n ^ j) p₁.1.2.b : Cˣ) * N'.uth (n ^ j) (I.φ b) (I.φ p₁.1.2.b) := by
  have hm : n ^ j ≠ 0 := hn.pow.pos.ne'
  obtain ⟨p, hp, rfl⟩ := exists_lift N hN _ (pow_ne_zero 2 hm) b hb
  obtain ⟨p', h, hp'⟩ := exists_partner μ hB (j * 2) _ (pow_mul n j 2).symm p
  replace hp' : p'.1.1 = 1 := by
    rw [hp, toAdd_one, map_zero] at hp'
    exact hp'
  have hb' : p'.1.2.b = I.φ p.1.2.b := by
    have key : ∀ K, K = n ^ (j * 2) → ∀ (q : N.QT K) (q' : N'.QT K), μ.r K q q' → q.1.1 = 1 → q'.1.1 = 1 →
        q'.1.2.b = I.φ q.1.2.b := by
      rintro K rfl
      exact hI _
    exact key _ (pow_mul n j 2).symm p p' h hp hp'
  have t := hT j p p' h hp hp' p₁.1.1.toAdd
  have w := μ.wp _ _ _ _ _ (r_powRep μ hm h hp hp') h₁
  rw [← he, txT_eq N' _ p' hp' (powRep N' _ p' hp') p₁' rfl rfl, txT_eq N _ p hp (powRep N _ p hp) p₁ rfl rfl, w,
    he, hb'] at t
  rw [uth_iso I _ hn.pow _ _ hb]
  refine mul_left_cancel₀ (N.wp (powRep N _ p hp) p₁).ne_zero ?_
  simp only [Units.val_mul] at t ⊢
  linear_combination ((I.lam : C) * ((I.h p₁.1.2.b ^ (n ^ j) ^ 2 : Cˣ) : C)) * t
end GlobalTheory.Ex.RecPeriods
