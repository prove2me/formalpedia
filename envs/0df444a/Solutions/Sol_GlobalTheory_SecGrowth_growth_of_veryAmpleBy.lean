-- Prove2me | solution 1 for GlobalTheory.SecGrowth.growth_of_veryAmpleBy
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:11:40.088366+00:00
-- url     : https://prove2.me/submissions/247638cd-fbcf-46de-85c7-b65c87d1fccc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsIndepSections
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FiniteOfNotLinearIndependent
import Theorems.Thm_P2M_GlobalTheory_SecGrowth_exists_isHomogeneous_eval_Hom_eq_1540398a731c
import Theorems.Thm_GlobalTheory_SecGrowth_sec_eq_zero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
noncomputable section
open GlobalTheory GlobalTheory.SecGrowth
namespace GlobalTheory.SecGrowth
theorem _root_.solution {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (CommRingCat.of K)) {H : LB X} {m : ℕ} (s : Fin (m + 1) → LB.Sec H) (hs : VeryAmpleBy f H s)
    (g t₀ : ℕ)
    (hgen : ∀ t : ℕ, t₀ ≤ t → ∀ σ : LB.Sec (pw H t), ∃ F : MvPolynomial (Fin (m + 1)) K, F.IsHomogeneous t ∧
      ∀ k : H.ι, σ.f k = MvPolynomial.eval₂Hom (cst f (H.U k)) (fun j => (s j).f k) F)
    (hGK : ∀ (B : Type) [CommRing B] [IsDomain B] [Algebra K B] (r : Fin (m + 1) → B),
      Function.Surjective (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B) → Algebra.trdeg K B = g →
      ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t →
        t ^ g ≤ c * Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
          (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B).toLinearMap) ∧
        Module.finrank K ((MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
          (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] B).toLinearMap) ≤ C * t ^ g)
    (htr : ∀ (B : Type) [CommRing B] [Nontrivial B] [Algebra K B] (j : Spec (CommRingCat.of B) ⟶ X),
      IsOpenImmersion j → j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap K B)) → Algebra.trdeg K B = g)
    (V : ℕ → Type) [∀ t, AddCommGroup (V t)] [∀ t, Module K (V t)] [∀ t, Module.Finite K (V t)]
    (ev : ∀ t : ℕ, V t → LB.Sec (pw H t))
    (hadd : ∀ t a b (k : H.ι), (ev t (a + b)).f k = (ev t a).f k + (ev t b).f k)
    (hsmul : ∀ t (c : K) a (k : H.ι), (ev t (c • a)).f k = cst f (H.U k) c * (show Γ(X, H.U k) from (ev t a).f k))
    (hinj : ∀ t a, (∀ k : H.ι, (ev t a).f k = 0) → a = 0)
    (hsurj : ∀ (t : ℕ) (σ : LB.Sec (pw H t)), ∃ a, ∀ k : H.ι, (ev t a).f k = σ.f k) :
    ∃ c C : ℕ, 1 ≤ c ∧ ∀ t : ℕ, 1 ≤ t →
      t ^ g ≤ c * Module.finrank K (V t) ∧ Module.finrank K (V t) ≤ C * t ^ g := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have hx : x ∈ ⨆ i, nonzeroLocus (s i) := by rw [hs.1]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨k₀, hk₀⟩ := TopologicalSpace.Opens.mem_iSup.1 hi
  obtain ⟨hD, r, hr, hrs⟩ := hs.2 i
  let W : X.Opens := X.basicOpen ((s i).f k₀)
  have hWD : W ≤ nonzeroLocus (s i) := le_iSup (fun k => X.basicOpen ((s i).f k)) k₀
  have hWU : W ≤ H.U k₀ := X.basicOpen_le _
  haveI : Nonempty W := ⟨⟨x, hk₀⟩⟩
  haveI : Nonempty (nonzeroLocus (s i)) := ⟨⟨x, hi⟩⟩
  obtain ⟨u, hu⟩ : IsUnit (rs X hWU ((s i).f k₀)) := X.toRingedSpace.isUnit_res_basicOpen _
  letI : Algebra K Γ(X, nonzeroLocus (s i)) := (cst f _).toAlgebra
  letI : Algebra K Γ(X, W) := (cst f _).toAlgebra
  let ρ : Γ(X, nonzeroLocus (s i)) →ₐ[K] Γ(X, W) :=
    { rs X hWD with commutes' := fun c => rs_cst f hWD c }
  have hρ : Function.Injective ρ := map_injective_of_isIntegral X (homOfLE hWD)
  have hsr : ∀ j, rs X hWU ((s j).f k₀) = u.val * rs X hWD (r j) := fun j => by
    have h := congrArg (rs X (le_inf hWD hWU)) (hr j k₀)
    rw [map_mul, rs_rs, rs_rs, rs_rs, ← hu] at h
    exact h.trans (mul_comm _ _)
  have hri : r i = 1 := by
    apply hρ
    have h := hsr i
    rw [← hu] at h
    rw [map_one]
    exact (Units.mul_right_inj u).1 (h.symm.trans (_root_.mul_one _).symm)
  have key : ∀ (t : ℕ) (F : MvPolynomial (Fin (m + 1)) K), F.IsHomogeneous t →
      rs X hWU (MvPolynomial.eval₂Hom (cst f (H.U k₀)) (fun j => (s j).f k₀) F) * (u⁻¹).val ^ t =
        ρ (MvPolynomial.aeval r F) := fun t F hF => by
    rw [rs_eval₂Hom, funext hsr, eval₂Hom_mul_of_isHomogeneous _ _ _ hF, ← rs_eval₂Hom, mul_right_comm,
      ← mul_pow, Units.mul_inv, one_pow, _root_.one_mul]
    rfl
  let Φ : ∀ t : ℕ, V t →ₗ[K] Γ(X, W) := fun t =>
    { toFun := fun a => rs X hWU ((ev t a).f k₀) * (u⁻¹).val ^ t
      map_add' := fun a b => by
        rw [hadd]
        exact (congrArg (· * _) (map_add (rs X hWU) _ _)).trans (add_mul _ _ _)
      map_smul' := fun c a => by
        rw [hsmul, map_mul, rs_cst, _root_.mul_assoc]
        rfl }
  have hΦ : ∀ t, Function.Injective (Φ t) := fun t => by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro a ha
    have h : rs X hWU ((ev t a).f k₀) = 0 := ((u⁻¹.isUnit.pow t).mul_left_eq_zero).1 ha
    exact hinj t a (sec_eq_zero (M := pw H t) (ev t a) (k₀ := k₀) hWU h)
  let P : ℕ → Submodule K Γ(X, nonzeroLocus (s i)) := fun t =>
    (MvPolynomial.restrictTotalDegree (Fin (m + 1)) K t).map
      (MvPolynomial.aeval r : MvPolynomial (Fin (m + 1)) K →ₐ[K] Γ(X, nonzeroLocus (s i))).toLinearMap
  have hP : ∀ t, Module.finrank K ((P t).map ρ.toLinearMap) = Module.finrank K (P t) := fun t =>
    (Submodule.equivMapOfInjective ρ.toLinearMap hρ (P t)).finrank_eq.symm
  have hV : ∀ t, Module.finrank K (LinearMap.range (Φ t)) = Module.finrank K (V t) := fun t =>
    LinearMap.finrank_range_of_inj (hΦ t)
  have hle : ∀ t, (P t).map ρ.toLinearMap ≤ LinearMap.range (Φ t) := by
    rintro t _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    obtain ⟨F, hF, hFp⟩ := exists_isHomogeneous_eval₂Hom_eq (cst f _) r i hri p
      ((MvPolynomial.mem_restrictTotalDegree _ _ _).1 hp)
    obtain ⟨a, ha⟩ := hsurj t (polySec f s hF)
    refine ⟨a, ?_⟩
    change rs X hWU ((ev t a).f k₀) * (u⁻¹).val ^ t = _
    rw [ha]
    exact (key t F hF).trans (congrArg ρ hFp)
  have hge : ∀ t, t₀ ≤ t → LinearMap.range (Φ t) ≤ (P t).map ρ.toLinearMap := by
    rintro t ht _ ⟨a, rfl⟩
    obtain ⟨F, hF, hFa⟩ := hgen t ht (ev t a)
    refine ⟨_, ⟨F, (MvPolynomial.mem_restrictTotalDegree _ _ _).2 hF.totalDegree_le, rfl⟩, ?_⟩
    change _ = rs X hWU ((ev t a).f k₀) * (u⁻¹).val ^ t
    rw [hFa]
    exact (key t F hF).symm
  have htd : Algebra.trdeg K Γ(X, nonzeroLocus (s i)) = g := by
    refine htr Γ(X, nonzeroLocus (s i)) hD.fromSpec inferInstance ?_
    have h := IsAffineOpen.SpecMap_appLE_fromSpec f (isAffineOpen_top _) hD le_top
    rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv, ← Spec.map_comp] at h
    exact h.symm
  obtain ⟨c, C, hc, hcC⟩ := hGK Γ(X, nonzeroLocus (s i)) r hrs htd
  refine ⟨c, C + ∑ t ∈ Finset.range t₀, Module.finrank K (V t), hc, fun t ht => ⟨?_, ?_⟩⟩
  · refine (hcC t ht).1.trans (Nat.mul_le_mul_left _ ?_)
    exact (hP t).symm.trans_le ((Submodule.finrank_mono (hle t)).trans (hV t).le)
  · by_cases h : t₀ ≤ t
    · refine le_trans ?_ ((hcC t ht).2.trans (Nat.mul_le_mul_right _ (Nat.le_add_right _ _)))
      rw [← hV, le_antisymm (hge t h) (hle t)]
      exact (hP t).le
    · have h₁ : Module.finrank K (V t) ≤ ∑ t ∈ Finset.range t₀, Module.finrank K (V t) :=
        Finset.single_le_sum (f := fun t => Module.finrank K (V t)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_range.2 (not_le.1 h))
      exact h₁.trans ((Nat.le_add_left _ C).trans (Nat.le_mul_of_pos_right _ (Nat.pow_pos ht)))
end GlobalTheory.SecGrowth
