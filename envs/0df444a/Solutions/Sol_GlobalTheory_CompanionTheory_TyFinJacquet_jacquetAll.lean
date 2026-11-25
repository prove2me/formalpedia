-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.TyFinJacquet.jacquetAll
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:16.524671+00:00
-- url     : https://prove2.me/submissions/4c741524-32b2-4b8e-96ad-535e2eda5a79

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_FiniteTypeHarishChandra_SupportExistsAll
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductSimpleAllStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SimpleIffIrreducibleStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_JacquetModuleAll
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_unip_of_levi
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_hasFixed_exists
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_hasFixed_le
import Theorems.Thm_GlobalTheory_CompanionTheory_TyFinJacquet_cusp_step
import Theorems.Thm_GlobalTheory_T_product_simple_all
import Theorems.Thm_GlobalTheory_T_simple_iff_irreducible


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory
open Formalism.IrreducibleCountingLemmas.TYPES hiding zIdem IsCuspidal
open ReciprocityTheory.Ty.Fin
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.TyFinJacquet
variable {K : Type} [Field K] [Fintype K] [DecidableEq K]
  {ι : Type} [Fintype ι] [DecidableEq ι] {s : ℕ}
namespace GlobalTheory.CompanionTheory.TyFinJacquet
theorem _root_.solution : ReciprocityTheory.Ty.Fin.St.JacquetAll := by
  intro K _ _ _ ι _ _ τ hτ
  have hirrτ := ((GlobalTheory.T.simple_iff_irreducible).1 _ τ).1 hτ
  haveI : Nontrivial τ := hirrτ.1
  classical
  obtain ⟨s₀, h₀⟩ := hasFixed_exists τ
  obtain ⟨m, hm, hmax⟩ : ∃ m, HasFixed τ m ∧ ∀ s', HasFixed τ s' → s' ≤ m :=
    ⟨Nat.findGreatest (HasFixed τ) (Fintype.card ι), Nat.findGreatest_spec (hasFixed_le h₀) h₀,
      fun s' h => Nat.le_findGreatest (hasFixed_le h) h⟩
  obtain ⟨b, hb, v, hv, hfix⟩ := hm
  haveI : Nontrivial (fixSub τ b) :=
    ⟨⟨⟨v, hfix⟩, 0, fun e => hv (congrArg Subtype.val e)⟩⟩
  obtain ⟨lam, Φ', hsimple, hΦ', heq'⟩ :=
    (GlobalTheory.T.product_simple_all : PI.GreenHCLabel.ProdSimple) m (fun c => GL {i // b i = c} K) (fixSub τ b) (wRep τ b)
  have hΦ : (fixSub τ b).subtype ∘ₗ Φ' ≠ 0 := by
    intro h
    apply hΦ'
    ext x
    have := LinearMap.congr_fun h (PiTensorProduct.tprod ℂ x)
    simpa using this
  have heq : ∀ p : parab K b, ((fixSub τ b).subtype ∘ₗ Φ') ∘ₗ infl K b lam p = τ.ρ p.1 ∘ₗ ((fixSub τ b).subtype ∘ₗ Φ') := by
    intro p
    ext x
    have h1 := LinearMap.congr_fun (heq' (leviHom b p)) (PiTensorProduct.tprod ℂ x)
    have h2 : ((Φ' (PiTensorProduct.map (fun c => (lam c).ρ (leviHom b p c)) (PiTensorProduct.tprod ℂ x)) : fixSub τ b) : τ) =
        τ.ρ (dGL b (leviHom b p)) (Φ' (PiTensorProduct.tprod ℂ x)) := by
      have := congrArg Subtype.val h1
      exact this
    have h3 : τ.ρ p.1 (Φ' (PiTensorProduct.tprod ℂ x)) = τ.ρ (dGL b (leviHom b p)) (Φ' (PiTensorProduct.tprod ℂ x)) := by
      have h4 := (Φ' (PiTensorProduct.tprod ℂ x)).2 _ (unip_of_levi b p)
      have e : p.1 = dGL b (leviHom b p) * ((dGL b (leviHom b p))⁻¹ * p.1) := by group
      calc τ.ρ p.1 (Φ' (PiTensorProduct.tprod ℂ x))
          = τ.ρ (dGL b (leviHom b p) * ((dGL b (leviHom b p))⁻¹ * p.1)) (Φ' (PiTensorProduct.tprod ℂ x)) := by rw [← e]
        _ = τ.ρ (dGL b (leviHom b p)) (τ.ρ ((dGL b (leviHom b p))⁻¹ * p.1) (Φ' (PiTensorProduct.tprod ℂ x))) := by
            rw [map_mul]; rfl
        _ = _ := by rw [h4]
    show ((Φ' (PiTensorProduct.map (fun c => (lam c).ρ (leviHom b p c)) (PiTensorProduct.tprod ℂ x)) : fixSub τ b) : τ) =
      τ.ρ p.1 (Φ' (PiTensorProduct.tprod ℂ x))
    rw [h2, h3]
  refine ⟨m, b, lam, (fixSub τ b).subtype ∘ₗ Φ', hb, fun c => ⟨hsimple c, ?_⟩, hΦ, heq⟩
  intro t b₁ hb₁ ht w hw
  by_contra hne
  have hirr := ((GlobalTheory.T.simple_iff_irreducible).1 _ (lam c)).1 (hsimple c)
  have := hmax _ (cusp_step hb hΦ heq c hirr (by omega) b₁ hb₁ w hne hw)
  omega
end GlobalTheory.CompanionTheory.TyFinJacquet
