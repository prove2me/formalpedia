-- Prove2me | solution 1 for GlobalTheory.AbCoh.CohBaseChange.of_parts
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:07:55.070031+00:00
-- url     : https://prove2.me/submissions/1d850791-7958-476f-ad78-4b04a22a085e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_AxesVanishingStructureSheafDegOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_IsScalarTowerOfAlgebraMapEq
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__AbelianHodgeDeRham_0e03413a4fcf6a02
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SpMapAlgHomAlgebraMap
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_exists_equiv_of_ker
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_dB_ext
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_spMap_algHom_algebraMap
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_isPullback_self
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_liftsAt_of
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_bc_of
import Theorems.Thm_GlobalTheory_AbCoh_CohBaseChange_liftsAt_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbCoh GlobalTheory.AbCoh.CohBaseChange
variable {R : Type} [CommRing R]
variable {X : Scheme.{0}} {s : X ⟶ Sp R} {K : CochainComplex (ModuleCat.{0} R) ℕ}
namespace GlobalTheory.AbCoh.CohBaseChange
theorem _root_.solution (hex : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) ∧ (∃ n, ∀ p, n < p → IsZero (K.X p)) ∧ Nonempty (Model s K))
    (halg : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∃ n, ∀ p, n < p → IsZero (K.X p)) → (∀ i, i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → LiftsAt K α i) → ∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom))
    (hsplit : ∀ (R : Type) [CommRing R] (K : CochainComplex (ModuleCat.{0} R) ℕ), (∀ p, Module.Finite R (K.X p) ∧ Module.Projective R (K.X p)) → (∀ i, i ≤ 2 → Module.Projective R (K.X (i + 1) ⧸ LinearMap.range (K.d i (i + 1)).hom)) → ∀ i, 1 ≤ i → i ≤ 2 → ∀ (R' : Type) [CommRing R'] [Algebra R R'], ∃ (P : Type) (_ : AddCommGroup P) (_ : Module R P) (_ : Module.Finite R P) (_ : Module.Projective R P) (u : LinearMap.ker (dB K R i (i + 1)) →ₗ[R] P) (v : LinearMap.ker (dB K R' i (i + 1)) →ₗ[R'] R' ⊗[R] P), Function.Surjective u ∧ Function.Surjective v ∧ (∀ z, u z = 0 ↔ z.1 ∈ LinearMap.range (dB K R (i - 1) i)) ∧ (∀ z, v z = 0 ↔ z.1 ∈ LinearMap.range (dB K R' (i - 1) i)) ∧ ∀ z z', z'.1 = ext (Algebra.ofId R R') _ z.1 → v z' = 1 ⊗ₜ u z) :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsProper s → Flat s → UConst s → (∀ (R' : Type) [CommRing R'] [Algebra R R'] [IsArtinianRing R'] [IsLocalRing R'] (k : Type) [Field k] [Algebra R k] (α : R' →ₐ[R] k), Function.Surjective α → ∀ (X' : Scheme.{0}) (s' : X' ⟶ Sp R') (φ : X' ⟶ X) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp k) (ψ : X₀ ⟶ X'), IsPullback φ s' s (spMap (algebraMap R R')) → ∀ w : IsPullback ψ s₀ s' (spMap (α : R' →+* k)), Function.Surjective (pullHO1 w.w) ∧ Function.Surjective (pullHO2 w.w)) → (Module.Finite R (HO1 s) ∧ Module.Projective R (HO1 s)) ∧ (Module.Finite R (HO2 s) ∧ Module.Projective R (HO2 s)) ∧ StructureSheafH1BaseChange s ∧ StructureSheafH2BaseChange s := by
  intro R _ _ X s hp hf hU hl
  obtain ⟨K, hK, hb, ⟨M⟩⟩ := hex R X s hp hf
  have hproj := halg R K hK hb (by
    intro i hi R' _ _ _ _ k _ _ α hα
    have h' := IsPullback.of_hasPullback s (spMap (algebraMap R R'))
    have w := IsPullback.of_hasPullback (pullback.snd s (spMap (algebraMap R R'))) (spMap (α : R' →+* k))
    have h₀ := w.paste_horiz h'
    rw [spMap_algHom_algebraMap] at h₀
    obtain ⟨s1, s2⟩ := hl R' k α hα _ _ _ _ _ _ h' w
    obtain ⟨n1, n2⟩ := M.nat h' h₀ α _ w.w rfl
    obtain ⟨a1, -, a2, -⟩ := M.exact h'
    obtain ⟨-, b1, -, b2⟩ := M.exact h₀
    interval_cases i
    · exact liftsAt_zero M hU α hα
    · exact liftsAt_of K α 1 (M.θ1 h') (M.θ1 h₀) _ a1 b1 n1 s1
    · exact liftsAt_of K α 2 (M.θ2 h') (M.θ2 h₀) _ a2 b2 n2 s2)
  have hid := isPullback_self s
  obtain ⟨a1, b1, a2, b2⟩ := M.exact hid
  have hz : ∀ (R' : Type) [CommRing R'] [Algebra R R'] (i : ℕ) (z : LinearMap.ker (dB K R i (i + 1))),
      ext (Algebra.ofId R R') _ z.1 ∈ LinearMap.ker (dB K R' i (i + 1)) := fun R' _ _ i z ↦ by
    rw [LinearMap.mem_ker, dB_ext, LinearMap.mem_ker.1 z.2, map_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ1 hid) hu a1 fun z ↦ (ku z).trans (b1 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · obtain ⟨P, _, _, _, _, u, v, hu, -, ku, -⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R
    obtain ⟨e, -⟩ := exists_equiv_of_ker u (M.θ2 hid) hu a2 fun z ↦ (ku z).trans (b2 z).symm
    exact ⟨Module.Finite.equiv e, Module.Projective.of_equiv e⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 1 le_rfl (by norm_num) R'
    obtain ⟨c1, d1, -, -⟩ := M.exact h
    obtain ⟨n1, -⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ1 hid) (M.θ1 h) _ hu hv a1 c1 (fun z ↦ (b1 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d1 z).symm) fun z ↦ ⟨⟨_, hz R' 1 z⟩, hn _ _ rfl, n1 _ _ rfl⟩
  · intro R' _ _ X' s' φ h
    obtain ⟨P, _, _, _, _, u, v, hu, hv, ku, kv, hn⟩ := hsplit R K hK hproj 2 (by norm_num) le_rfl R'
    obtain ⟨-, -, c2, d2⟩ := M.exact h
    obtain ⟨-, n2⟩ := M.nat hid h (Algebra.ofId R R') φ h.w (Category.comp_id _)
    exact bc_of u v (M.θ2 hid) (M.θ2 h) _ hu hv a2 c2 (fun z ↦ (b2 z).trans (ku z).symm)
      (fun z ↦ (kv z).trans (d2 z).symm) fun z ↦ ⟨⟨_, hz R' 2 z⟩, hn _ _ rfl, n2 _ _ rfl⟩
end GlobalTheory.AbCoh.CohBaseChange
