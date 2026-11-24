-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.RgFl.StarPf.stStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:25:20.253397+00:00
-- url     : https://prove2.me/submissions/2dc46749-aa4e-4e4f-87eb-bc94aac2e341

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_HarishChandraModules_KFiniteAnalyticVectors_AdmissibleSmoothVectors_SmallPI
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_StatementStar
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_StarPf_restrictAlg_coe
import Theorems.Thm_GlobalTheory_CompanionTheory_RgFl_StarPf_inf_orthogonal_invariant
import Theorems.Thm_CompanionTheory_D_gk_admitted_small_irreducible_representation
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


section
noncomputable section
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace
namespace GlobalTheory.CompanionTheory.RgFl.StarPf
section
variable {A V : Type} [Ring A] [Algebra ℂ A]
end
private theorem map_word_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (l : List A) : f (word 1 l) = word 1 (l.map f) := by
  induction l with
  | nil =>
    show f 1 = 1
    exact map_one f
  | cons a l ih =>
    show f (1 * a * word 1 l) = 1 * f a * word 1 (l.map f)
    rw [map_mul, map_mul, map_one, ih]
private theorem map_stdPoly_one {A B : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) {M : ℕ} (b : Fin M → A) : f (stdPoly 1 b) = stdPoly 1 (fun i => f (b i)) := by
  unfold stdPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [map_mul, map_intCast, map_word_one, List.map_ofFn]
  rfl
end GlobalTheory.CompanionTheory.RgFl.StarPf
end
end

set_option autoImplicit false
noncomputable section
open CompanionTheory.Rg.Fl CompanionTheory.D.gk.admitted
open scoped InnerProductSpace
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgFl GlobalTheory.CompanionTheory.RgFl.StarPf
namespace GlobalTheory.CompanionTheory.RgFl.StarPf
theorem _root_.solution : StStar := by
  unfold StStar
  intro C A _ _ hirr
  suffices key : ∀ n : ℕ, ∀ (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V],
      Module.finrank ℂ V = n → ∀ (ρ : A →ₐ[ℂ] Module.End ℂ V), StarClosed ρ →
        ∀ (b : Fin (C ^ 2 + 1) → A), ρ (stdPoly 1 b) = 0 by
    intro V _ _ _ ρ hs b
    exact key _ V rfl ρ hs b
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ hn ρ hs b
  classical
  rcases Nat.eq_zero_or_pos n with hn0 | hnpos
  · have : Subsingleton V := Module.finrank_zero_iff.mp (hn.trans hn0)
    exact LinearMap.ext fun v => Subsingleton.elim _ _
  have : Nontrivial V := Module.finrank_pos_iff.mp (hn ▸ hnpos)
  have hex : ∃ d, ∃ W : Submodule ℂ V, ((∀ h, ∀ w ∈ W, ρ h w ∈ W) ∧ W ≠ ⊥) ∧ Module.finrank ℂ W = d :=
    ⟨_, ⊤, ⟨fun _ _ _ => Submodule.mem_top, bot_ne_top.symm⟩, rfl⟩
  obtain ⟨W, ⟨hWinv, hWne⟩, hWd⟩ := Nat.find_spec hex
  have hmin : ∀ W' : Submodule ℂ V, (∀ h, ∀ w ∈ W', ρ h w ∈ W') → W' ≠ ⊥ →
      Module.finrank ℂ W ≤ Module.finrank ℂ W' := by
    intro W' h1 h2
    rw [hWd]
    exact Nat.find_min' hex ⟨W', ⟨h1, h2⟩, rfl⟩
  have hWirr : ∀ U : Submodule ℂ W, (∀ h, ∀ u ∈ U, restrictAlg ρ W hWinv h u ∈ U) → U = ⊥ ∨ U = ⊤ := by
    intro U hU
    by_cases hUb : U = ⊥
    · exact Or.inl hUb
    right
    have hU'inv : ∀ h, ∀ v ∈ U.map W.subtype, ρ h v ∈ U.map W.subtype := by
      intro h v hv
      obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hv
      exact Submodule.mem_map.mpr ⟨restrictAlg ρ W hWinv h u, hU h u hu, restrictAlg_coe ρ W hWinv h u⟩
    have hfr : Module.finrank ℂ (U.map W.subtype) = Module.finrank ℂ U := Submodule.finrank_map_subtype_eq W U
    have hU'ne : U.map W.subtype ≠ ⊥ := by
      intro h0
      apply hUb
      apply Submodule.finrank_eq_zero.mp
      rw [← hfr]
      exact Submodule.finrank_eq_zero.mpr h0
    have h1 := hmin _ hU'inv hU'ne
    apply Submodule.eq_top_of_finrank_eq
    exact le_antisymm (Submodule.finrank_le U) (hfr ▸ h1)
  have hdimW : Module.finrank ℂ W ≤ C := hirr W (restrictAlg ρ W hWinv) hWirr
  have hlt : Module.finrank ℂ W ^ 2 < C ^ 2 + 1 := Nat.lt_succ_of_le (Nat.pow_le_pow_left hdimW 2)
  have hPW : ∀ w ∈ W, ρ (stdPoly 1 b) w = 0 := by
    intro w hw
    rw [map_stdPoly_one ρ b]
    exact CompanionTheory.D.gk.admitted.small_irreducible_representation V W W le_rfl 1 (fun w hw => hw) (C ^ 2 + 1) hlt (fun i => ρ (b i))
      (fun i w hw => hWinv (b i) w hw) w hw
  have hperp : ∀ h, ∀ x ∈ Wᗮ, ρ h x ∈ Wᗮ := by
    intro h x hx
    have h1 := inf_orthogonal_invariant ρ hs (U := W) (W := ⊤) hWinv (fun _ _ _ => Submodule.mem_top) h x
      (Submodule.mem_inf.mpr ⟨hx, Submodule.mem_top⟩)
    exact (Submodule.mem_inf.mp h1).1
  have hs2 : StarClosed (restrictAlg ρ Wᗮ hperp) := by
    intro h
    obtain ⟨h', hh'⟩ := hs h
    refine ⟨h', fun u w => ?_⟩
    rw [Submodule.coe_inner, Submodule.coe_inner, restrictAlg_coe, restrictAlg_coe]
    exact hh' u w
  have hWpos : 0 < Module.finrank ℂ W := Nat.pos_of_ne_zero fun h0 => hWne (Submodule.finrank_eq_zero.mp h0)
  have hsum := Submodule.finrank_add_finrank_orthogonal W
  have hltp : Module.finrank ℂ Wᗮ < n := by omega
  have hrest := ih _ hltp Wᗮ rfl (restrictAlg ρ Wᗮ hperp) hs2 b
  have hPperp : ∀ x ∈ Wᗮ, ρ (stdPoly 1 b) x = 0 := by
    intro x hx
    have h0 := congrArg (fun T => ((T ⟨x, hx⟩ : Wᗮ) : V)) hrest
    simpa [restrictAlg_coe] using h0
  refine LinearMap.ext fun v => ?_
  have hv : v ∈ W ⊔ Wᗮ := by
    have htop : W ⊔ Wᗮ = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      have h1 := Submodule.finrank_sup_add_finrank_inf_eq W Wᗮ
      have h2 : W ⊓ Wᗮ = ⊥ := disjoint_iff.mp (Submodule.orthogonal_disjoint W)
      rw [h2, Submodule.finrank_eq_zero.mpr rfl] at h1
      omega
    rw [htop]
    exact Submodule.mem_top
  obtain ⟨w, hw, x, hx, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add, hPW w hw, hPperp x hx, add_zero, LinearMap.zero_apply]
end GlobalTheory.CompanionTheory.RgFl.StarPf
