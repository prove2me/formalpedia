-- Prove2me | solution 1 for GlobalTheory.CongruenceDet.isIntegral_det_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T13:57:20.30191+00:00
-- url     : https://prove2.me/submissions/9205f8d9-0558-4585-b395-fc36c9954ebe

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralDetSubOne
import Theorems.Thm_GlobalTheory_CongruenceDet_isIntegral_root

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CongruenceDet
open NumberField Matrix
open scoped nonZeroDivisors
namespace GlobalTheory.CongruenceDet
namespace _root_.GlobalTheory.CongruenceDet
theorem _root_.solution {R E : Type} [CommRing R] [Field E]
    [CharZero E]
    [Algebra R E] {r M : ℕ} (hM : M ≠ 0)
    (Λ : Submodule R (Fin r → E)) (g : Matrix (Fin r) (Fin r) E) (hfg : Λ.FG)
    (hspan : Submodule.span E (Λ : Set (Fin r → E)) = ⊤)
    (hg : ∀ v ∈ Λ, ∃ w ∈ Λ, g *ᵥ v = v + M • w) :
    IsIntegral R ((g.det - 1) / M) := by
  classical
  let K := AlgebraicClosure E

  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap E K).injective
  have hroots : ∀ μ ∈ (g.map (algebraMap E K)).charpoly.roots, IsIntegral R ((μ - 1) / M) :=
    fun μ hμ => _root_.GlobalTheory.CongruenceDet.isIntegral_root hM Λ g hfg hspan hg μ
      (Polynomial.isRoot_of_mem_roots hμ)
  have hMK : (M : K) ≠ 0 := by exact_mod_cast hM
  have hMint : IsIntegral R (M : K) := by
    simpa using isIntegral_algebraMap (R := R) (A := K) (x := (M : R))
  have hprod : ∀ s : Multiset K, (∀ μ ∈ s, IsIntegral R ((μ - 1) / M)) →
      IsIntegral R ((s.prod - 1) / M) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simpa using isIntegral_zero
    | cons a s ih =>
      intro hs
      have ha := hs a (Multiset.mem_cons_self a s)
      have hb := ih (fun μ hμ => hs μ (Multiset.mem_cons_of_mem hμ))
      have key : ((a ::ₘ s).prod - 1) / M =
          (a - 1) / M * (M * ((s.prod - 1) / M) + 1) + (s.prod - 1) / M := by
        rw [Multiset.prod_cons, mul_div_cancel₀ _ hMK]
        ring
      rw [key]
      exact (ha.mul ((hMint.mul hb).add isIntegral_one)).add hb
  have h1 : algebraMap E K g.det = (g.map (algebraMap E K)).det := by
    rw [RingHom.map_det]
    rfl
  have hK := hprod _ hroots
  rw [← Matrix.det_eq_prod_roots_charpoly, ← h1] at hK
  have hK' : IsIntegral R (IsScalarTower.toAlgHom R E K ((g.det - 1) / M)) := by
    simpa [map_div₀, map_sub, map_one, map_natCast] using hK
  exact (isIntegral_algHom_iff _ (algebraMap E K).injective).1 hK'
end _root_.GlobalTheory.CongruenceDet
end GlobalTheory.CongruenceDet
