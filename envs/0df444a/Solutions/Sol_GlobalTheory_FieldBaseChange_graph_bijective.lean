-- Prove2me | solution 1 for GlobalTheory.FieldBaseChange.graph_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:31:35.774921+00:00
-- url     : https://prove2.me/submissions/faeb15b9-0f10-45d9-b1f8-58ecbf177e31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IsExtensionOfIsPushout
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsCoord_natural
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_eq_of_coord
import Theorems.Thm_GlobalTheory_FieldBaseChange_IsExtension_exists_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.FieldBaseChange
variable {K F : Type} [Field K] [Field F] [Algebra K F]
variable {R : Type} [CommRing R] [IsDomain R] [Algebra R K] [IsFractionRing R K]
  {V₀ V V' W W' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module F W']
  {J : Type} {P₀ P P' : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
  [∀ j, AddCommGroup (P j)] [∀ j, Module K (P j)] [∀ j, AddCommGroup (P' j)] [∀ j, Module F (P' j)]
namespace GlobalTheory.FieldBaseChange
theorem _root_.solution (X : Submodule R (V₀ × ∀ j, P₀ j))
    (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : ∀ j, P₀ j →ₛₗ[algebraMap R K] P j)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a)
    (b : ∀ j, P j →ₛₗ[algebraMap K F] P' j) (hb : ∀ j, IsExtension (b j))
    (d : W →ₛₗ[algebraMap K F] W') (hd : IsExtension d)
    (π : ∀ j, W →ₗ[K] P j) (π' : ∀ j, W' →ₗ[F] P' j) (comm : ∀ j w, π' j (d w) = b j (π j w))
    (E : V → W → Prop)
    (hE : ∀ v w, E v w ↔ ∃ r : R, r ≠ 0 ∧ ∃ x ∈ X, ρ x.1 = algebraMap R K r • v ∧
      ∀ j, ρ' j (x.2 j) = algebraMap R K r • π j w)
    (bij : (∀ v, ∃! w, E v w) ∧ ∀ w, ∃! v, E v w)
    (E' : V' → W' → Prop)
    (hE' : ∀ v w, E' v w ↔ ∃ (n : ℕ) (c : Fin n → F) (x : Fin n → V₀ × ∀ j, P₀ j), (∀ i, x i ∈ X) ∧
      v = ∑ i, c i • a (ρ (x i).1) ∧ ∀ j, π' j w = ∑ i, c i • b j (ρ' j ((x i).2 j))) :
    (∀ v, ∃! w, E' v w) ∧ ∀ w, ∃! v, E' v w := by
  classical
  have key : ∀ v w, E' v w → ∀ (ℓ : F →ₗ[K] K) (Λa : V' →+ V) (Λd : W' →+ W),
      IsCoord a ℓ Λa → IsCoord d ℓ Λd → E (Λa v) (Λd w) := by
    intro v w hvw ℓ Λa Λd hΛa hΛd
    obtain ⟨n, c, x, hx, rfl, hw⟩ := (hE' v w).mp hvw
    choose Λb hΛb using fun j => (hb j).coord ℓ
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
      (fun i => ℓ (c i))
    choose s hs using fun i => RingHom.mem_rangeS.mp (ht i)
    have hcoef : ∀ i, algebraMap R K (s i) = algebraMap R K (t : R) * ℓ (c i) := by
      intro i; rw [hs i, Algebra.smul_def]
    rw [hE]
    refine ⟨t, nonZeroDivisors.ne_zero t.2, ∑ i, s i • x i,
      Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (hx i)), ?_, fun j => ?_⟩
    · rw [Prod.fst_sum, map_sum, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Prod.smul_fst, LinearMap.map_smulₛₗ, hΛa (c i) _, hcoef i, smul_smul]
    · have hnat := IsCoord.natural hd.span hΛd (hΛb j) (π j) (π' j) (comm j) w
      rw [← hnat, hw j, map_sum, Prod.snd_sum, Finset.sum_apply, map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Prod.smul_snd, Pi.smul_apply, LinearMap.map_smulₛₗ, hΛb j (c i) _, hcoef i, smul_smul]
  have hne : ∀ r : R, r ≠ 0 → algebraMap K F (algebraMap R K r) ≠ 0 := fun r hr =>
    (map_ne_zero _).mpr ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr)
  have hcancel : ∀ (c : F) (r : R), r ≠ 0 →
      (c * (algebraMap K F (algebraMap R K r))⁻¹) * algebraMap K F (algebraMap R K r) = c :=
    fun c r hr => by rw [mul_assoc, inv_mul_cancel₀ (hne r hr), mul_one]
  refine ⟨fun v => ?_, fun w => ?_⟩
  · obtain ⟨n, c, u, rfl⟩ := ha.exists_sum v
    choose φ hφ using fun i => (bij.1 (u i)).exists
    choose r hr y hy hy₁ hy₂ using fun i => (hE _ _).mp (hφ i)
    have h₀ : E' (∑ i, c i • a (u i)) (∑ i, c i • d (φ i)) := by
      rw [hE']
      refine ⟨n, fun i => c i * (algebraMap K F (algebraMap R K (r i)))⁻¹, y, hy, ?_, fun j => ?_⟩
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hy₁, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
      · rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, comm, hy₂, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
    refine ⟨_, h₀, fun w' hw' => hd.eq_of_coord (fun ℓ Λd hΛd => ?_)⟩
    obtain ⟨Λa, hΛa⟩ := ha.coord ℓ
    exact (bij.1 _).unique (key _ _ hw' ℓ Λa Λd hΛa hΛd) (key _ _ h₀ ℓ Λa Λd hΛa hΛd)
  · obtain ⟨n, c, u, rfl⟩ := hd.exists_sum w
    choose φ hφ using fun i => (bij.2 (u i)).exists
    choose r hr y hy hy₁ hy₂ using fun i => (hE _ _).mp (hφ i)
    have h₀ : E' (∑ i, c i • a (φ i)) (∑ i, c i • d (u i)) := by
      rw [hE']
      refine ⟨n, fun i => c i * (algebraMap K F (algebraMap R K (r i)))⁻¹, y, hy, ?_, fun j => ?_⟩
      · refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hy₁, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
      · rw [map_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [map_smul, comm, hy₂, LinearMap.map_smulₛₗ, smul_smul, hcancel _ _ (hr i)]
    refine ⟨_, h₀, fun v' hv' => ha.eq_of_coord (fun ℓ Λa hΛa => ?_)⟩
    obtain ⟨Λd, hΛd⟩ := hd.coord ℓ
    exact (bij.2 _).unique (key _ _ hv' ℓ Λa Λd hΛa hΛd) (key _ _ h₀ ℓ Λa Λd hΛa hΛd)
end GlobalTheory.FieldBaseChange
