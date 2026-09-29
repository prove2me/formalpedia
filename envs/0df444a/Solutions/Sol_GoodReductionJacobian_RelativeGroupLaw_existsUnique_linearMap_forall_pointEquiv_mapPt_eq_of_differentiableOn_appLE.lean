-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/9cdde696-ac90-5027-a868-5b8f117a7dde

import Mathlib
import Theorems.Thm_Complex_contDiffOn_one_of_differentiableOn_pi
import Definitions.Def_CerednikDrinfeld_QMModuli
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian CerednikDrinfeld.QM Topology
open Metric Filter Set

namespace BenchNK4b

theorem exists_pos_forall_norm_lt_eq_zero {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ))
    (hΛ : ∃ b₀ : Module.Basis (Fin (2 * g)) ℝ (Fin g → ℂ), Λ = Submodule.span ℤ (Set.range b₀)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ v ∈ Λ, ‖v‖ < δ → v = 0 := by
  obtain ⟨b₀, rfl⟩ := hΛ

  have hdisc : IsDiscrete ((Submodule.span ℤ (Set.range b₀) : Submodule ℤ (Fin g → ℂ)) : Set (Fin g → ℂ)) :=
    isDiscrete_iff_discreteTopology.mpr (inferInstance : DiscreteTopology (Submodule.span ℤ (Set.range b₀)))
  obtain ⟨δ, hδ, h⟩ := Metric.exists_ball_inter_eq_singleton_of_mem_discrete hdisc
    (x := (0 : Fin g → ℂ)) (Submodule.zero_mem _)
  refine ⟨δ, hδ, fun v hv hvδ => ?_⟩
  have : v ∈ ball (0 : Fin g → ℂ) δ ∩ (Submodule.span ℤ (Set.range b₀) : Set (Fin g → ℂ)) :=
    ⟨by rwa [mem_ball, dist_zero_right], hv⟩
  rw [h] at this
  exact this

theorem eq_fderiv_of_locally_additive {V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {ℓ : V → W} {ρ : ℝ} (hρ : 0 < ρ)
    (hadd : ∀ v w : V, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → ℓ (v + w) = ℓ v + ℓ w)
    {T : V →L[ℂ] W} (hT : HasFDerivAt ℓ T 0) :
    ∀ v : V, ‖v‖ < ρ → ℓ v = T v := by
  have h0 : ℓ 0 = 0 := by
    have := hadd 0 0 (by simpa using hρ) (by simpa using hρ) (by simpa using hρ)
    simpa using this

  have hmul : ∀ (x : V) (n : ℕ), (n : ℝ) * ‖x‖ < ρ → ℓ ((n : ℂ) • x) = (n : ℂ) • ℓ x := by
    intro x n hn
    induction n with
    | zero => simp [h0]
    | succ k ih =>
      have hk : (k : ℝ) * ‖x‖ < ρ := lt_of_le_of_lt (by gcongr; norm_num) hn
      have hx : ‖x‖ < ρ :=
        lt_of_le_of_lt (le_mul_of_one_le_left (norm_nonneg x) (by simp)) hn
      have e1 : ((k + 1 : ℕ) : ℂ) • x = (k : ℂ) • x + x := by push_cast; rw [add_smul, one_smul]
      rw [e1, hadd _ _ ?_ hx ?_, ih hk]
      · push_cast; rw [add_smul, one_smul]
      · rw [norm_smul]; simpa using hk
      · rw [← e1, norm_smul]; push_cast
        rw [show ‖((k : ℂ) + 1)‖ = (k : ℝ) + 1 from by
          rw [show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]; push_cast; ring]
        simpa using hn
  intro v hv

  by_contra hne
  have hpos : 0 < ‖ℓ v - T v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  have hv0 : v ≠ 0 := by
    intro h; subst h; simp [h0] at hne
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0

  have hlo := hT.isLittleO
  rw [Asymptotics.isLittleO_iff] at hlo
  have hε : 0 < ‖ℓ v - T v‖ / (2 * ‖v‖) := by positivity
  have hev := hlo hε
  rw [h0] at hev

  rw [Filter.eventually_iff_exists_mem] at hev
  obtain ⟨s, hs, hsub⟩ := hev
  obtain ⟨η, hη, hball⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨n, hn⟩ := exists_nat_gt (‖v‖ / η)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set x : V := ((n : ℂ)⁻¹) • v with hx
  have hxn : (n : ℂ) • x = v := by
    rw [hx, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn0.ne'), one_smul]
  have hnormx : ‖x‖ = ‖v‖ / n := by
    rw [hx, norm_smul, norm_inv, Complex.norm_natCast, div_eq_inv_mul]
  have hxs : x ∈ s := by
    apply hball
    rw [mem_ball, dist_zero_right, hnormx, div_lt_iff₀ hnR]
    calc ‖v‖ = ‖v‖ / η * η := by field_simp
      _ < n * η := by gcongr
      _ = η * n := mul_comm _ _
  have hest := hsub x hxs
  simp only [sub_zero] at hest

  have hscale : ℓ v - T v = (n : ℂ) • (ℓ x - T x) := by
    rw [← hxn, hmul x n (by rw [hnormx]; field_simp; exact hv), map_smul, smul_sub]
  have : ‖ℓ v - T v‖ ≤ ‖ℓ v - T v‖ / 2 := by
    calc ‖ℓ v - T v‖ = (n : ℝ) * ‖ℓ x - T x‖ := by rw [hscale, norm_smul, Complex.norm_natCast]
      _ ≤ (n : ℝ) * (‖ℓ v - T v‖ / (2 * ‖v‖) * ‖x‖) := mul_le_mul_of_nonneg_left hest hnR.le
      _ = ‖ℓ v - T v‖ / 2 := by rw [hnormx]; field_simp
  linarith

theorem forall_eq_mk_of_eqOn_ball {g g' : ℕ} (Λ' : Submodule ℤ (Fin g' → ℂ))
    (H : (Fin g → ℂ) →+ ((Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)) (T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ))
    {ρ : ℝ} (hρ : 0 < ρ) (hloc : ∀ v : Fin g → ℂ, ‖v‖ < ρ → H v = ((T v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)) :
    ∀ v : Fin g → ℂ, H v = ((T v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) := by
  intro v
  obtain ⟨n, hn⟩ := exists_nat_gt (‖v‖ / ρ)
  have hn0 : 0 < n := by
    have : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
    exact_mod_cast this
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set x : Fin g → ℂ := ((n : ℂ)⁻¹) • v with hx
  have hxn : (n : ℕ) • x = v := by
    rw [hx, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, mul_inv_cancel₀ (by exact_mod_cast hn0.ne'), one_smul]
  have hxρ : ‖x‖ < ρ := by
    rw [hx, norm_smul, norm_inv, Complex.norm_natCast, inv_mul_lt_iff₀ hnR]
    calc ‖v‖ = ‖v‖ / ρ * ρ := by field_simp
      _ < n * ρ := by gcongr
  rw [← hxn, map_nsmul, hloc x hxρ, map_nsmul]
  rw [← QuotientAddGroup.mk_nsmul]

theorem linearMap_eq_of_forall_sub_mem {g g' : ℕ} (Λ' : Submodule ℤ (Fin g' → ℂ))
    (hΛ' : ∃ b₀ : Module.Basis (Fin (2 * g')) ℝ (Fin g' → ℂ), Λ' = Submodule.span ℤ (Set.range b₀))
    (T₁ T₂ : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)) (h : ∀ v, T₁ v - T₂ v ∈ Λ') : T₁ = T₂ := by
  obtain ⟨δ, hδ, hdisc⟩ := exists_pos_forall_norm_lt_eq_zero Λ' hΛ'
  refine LinearMap.ext fun v => ?_
  by_contra hne
  have hS : T₁ v - T₂ v ≠ 0 := sub_ne_zero.mpr hne
  have hpos : 0 < ‖T₁ v - T₂ v‖ := norm_pos_iff.mpr hS

  set t : ℂ := ((δ / (2 * ‖T₁ v - T₂ v‖) : ℝ) : ℂ) with ht
  have ht0 : t ≠ 0 := by
    rw [ht, Complex.ofReal_ne_zero]; positivity
  have hmem : T₁ (t • v) - T₂ (t • v) ∈ Λ' := h _
  have hnorm : ‖T₁ (t • v) - T₂ (t • v)‖ < δ := by
    rw [map_smul, map_smul, ← smul_sub, norm_smul, ht, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
    rw [div_mul_eq_mul_div, mul_div_assoc]
    have : ‖T₁ v - T₂ v‖ / (2 * ‖T₁ v - T₂ v‖) = 1 / 2 := by field_simp
    rw [this]; linarith
  have := hdisc _ hmem hnorm
  rw [map_smul, map_smul, ← smul_sub, smul_eq_zero] at this
  exact this.elim ht0 hS

section scheme

variable {G G' : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} {f' : G' ⟶ Spec (CommRingCat.of ℂ)}

theorem appLE_comp_apply (u : G ⟶ G') (P : Spec (CommRingCat.of ℂ) ⟶ G) (U' : G'.Opens) (φ : Γ(G', U'))
    (h : ⊤ ≤ (P ≫ u) ⁻¹ᵁ U') :
    ((P ≫ u).appLE U' ⊤ h) φ = (P.appLE (u ⁻¹ᵁ U') ⊤ h) (u.app U' φ) := by
  rw [Scheme.Hom.comp_appLE]
  rfl

theorem appLE_apply_congr_pt {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of ℂ)}
    {P Q : SchemeHomOver t f} (hPQ : P = Q) (U : G.Opens) (φ : Γ(G, U))
    (hP : ⊤ ≤ P.1 ⁻¹ᵁ U) (hQ : ⊤ ≤ Q.1 ⁻¹ᵁ U) :
    (P.1.appLE U ⊤ hP) φ = (Q.1.appLE U ⊤ hQ) φ := by
  subst hPQ; rfl

variable (L : RelativeGroupLaw ℂ f) (L' : RelativeGroupLaw ℂ f') {g g' : ℕ}
  (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin g' → ℂ))
  (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
  (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f' ≃ ((Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))
  (he : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
    e (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)
  (he' : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f',
    e' (L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e' P + e' Q)
  (u : G ⟶ G') (hu : u ≫ f' = f)
  (hhom : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
      mapPt u hu (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) =
        L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt u hu P) (mapPt u hu Q))

include he in
theorem equiv_one : e (L.one (𝟙 _)) = 0 := by
  have h := he (L.one (𝟙 _)) (L.one (𝟙 _))
  rw [L.one_mul] at h
  simpa using h

include he in
theorem equiv_symm_zero : e.symm 0 = L.one (𝟙 _) := by
  rw [Equiv.symm_apply_eq]; exact (equiv_one L Λ e he).symm

include he in
theorem equiv_symm_add (a b : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) :
    e.symm (a + b) = L.mul (𝟙 _) (e.symm a) (e.symm b) := by
  rw [Equiv.symm_apply_eq, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

include he' hhom in
theorem mapPt_one : mapPt u hu (L.one (𝟙 _)) = L'.one (𝟙 _) := by
  have h := hhom (L.one (𝟙 _)) (L.one (𝟙 _))
  rw [L.one_mul] at h
  apply e'.injective
  have h2 := congrArg e' h
  rw [he'] at h2
  rw [equiv_one L' Λ' e' he']
  simpa using h2

def inducedHom : (Fin g → ℂ) →+ ((Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) where
  toFun v := e' (mapPt u hu (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)))
  map_zero' := by
    show e' (mapPt u hu (e.symm ((0 : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ.toAddSubgroup))) = 0
    rw [QuotientAddGroup.mk_zero, equiv_symm_zero L Λ e he, mapPt_one L L' Λ' e' he' u hu hhom,
      equiv_one L' Λ' e' he']
  map_add' v w := by
    show e' (mapPt u hu (e.symm ((v + w : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ.toAddSubgroup))) =
      e' (mapPt u hu (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup))) +
      e' (mapPt u hu (e.symm (w : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)))
    rw [QuotientAddGroup.mk_add, equiv_symm_add L Λ e he, hhom, he']

theorem inducedHom_apply (v : Fin g → ℂ) :
    inducedHom L L' Λ Λ' e e' he he' u hu hhom v =
      e' (mapPt u hu (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup))) :=
  rfl

end scheme

end BenchNK4b

open BenchNK4b in
theorem solution
    {G G' : Scheme.{0}} {f : G ⟶ Spec (CommRingCat.of ℂ)} {f' : G' ⟶ Spec (CommRingCat.of ℂ)}
    (L : RelativeGroupLaw ℂ f) (L' : RelativeGroupLaw ℂ f') {g g' : ℕ}
    (Λ : Submodule ℤ (Fin g → ℂ)) (Λ' : Submodule ℤ (Fin g' → ℂ))
    (e : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f ≃ ((Fin g → ℂ) ⧸ Λ.toAddSubgroup))
    (e' : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f' ≃ ((Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))

    (hL1' : ∃ b₀ : Module.Basis (Fin (2 * g')) ℝ (Fin g' → ℂ), Λ' = Submodule.span ℤ (Set.range b₀))

    (he : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f, e (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e P + e Q)
    (he' : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f', e' (L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = e' P + e' Q)

    (hAN : ∀ (U : G.Opens) (φ : Γ(G, U)),
      IsOpen {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g → ℂ | ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g → ℂ) (h : ⊤ ≤ (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)).1.appLE U ⊤ h) φ)))

    (hAN' : ∀ (U : G'.Opens) (φ : Γ(G', U)),
      IsOpen {v : Fin g' → ℂ | ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
      ∃ F : (Fin g' → ℂ) → ℂ,
        DifferentiableOn ℂ F {v : Fin g' → ℂ | ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U} ∧
        ∀ (v : Fin g' → ℂ) (h : ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U),
          F v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h) φ)))

    (hCOV' : ∀ v₀ : Fin g' → ℂ,
      ∃ (U : G'.Opens) (t : Fin g' → Γ(G', U)) (ε : ℝ) (D : (Fin g' → ℂ) ≃L[ℂ] (Fin g' → ℂ))
        (F : (Fin g' → ℂ) → (Fin g' → ℂ)),
        0 < ε ∧
        (∀ v ∈ Metric.ball v₀ ε, ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U) ∧
        (∀ (v : Fin g' → ℂ) (h : ⊤ ≤ (e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U), v ∈ Metric.ball v₀ ε →
          F v = fun i : Fin g' => (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((((e'.symm (v : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h) (t i)))) ∧
        HasFDerivAt F (D : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) v₀)

    (hSURJ' : ∀ (v₀ : Fin g' → ℂ) (r : ℝ), 0 < r →
      ∃ (U : G'.Opens) (fs : Finset (Γ(G', U))) (ε : ℝ) (h₀ : ⊤ ≤ (e'.symm (v₀ : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1 ⁻¹ᵁ U), 0 < ε ∧
        ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f') (hP : ⊤ ≤ P.1 ⁻¹ᵁ U),
          (∀ φ ∈ fs, ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom ((P.1.appLE U ⊤ hP) φ) -
              (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((e'.symm (v₀ : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U ⊤ h₀) φ)‖ < ε) →
          ∃ w ∈ Metric.ball v₀ r, e' P = (w : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup))

    (u : G ⟶ G') (hu : u ≫ f' = f)
    (hhom : ∀ P Q : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f,
      mapPt u hu (L.mul (𝟙 (Spec (CommRingCat.of ℂ))) P Q) = L'.mul (𝟙 (Spec (CommRingCat.of ℂ))) (mapPt u hu P) (mapPt u hu Q)) :
    ∃! T : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ),
      (∀ v ∈ Λ, T v ∈ Λ') ∧
      ∀ (P : SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f) (v : Fin g → ℂ),
        e P = (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) →
        e' (mapPt u hu P) = ((T v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) := by
  classical

  set π : (Fin g → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f :=
    fun v => e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) with hπ
  set π' : (Fin g' → ℂ) → SchemeHomOver (𝟙 (Spec (CommRingCat.of ℂ))) f' :=
    fun w => e'.symm (w : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) with hπ'
  set H := inducedHom L L' Λ Λ' e e' he he' u hu hhom with hH
  have hHv : ∀ v, H v = e' (mapPt u hu (π v)) := fun v => rfl

  have hπ0 : π 0 = L.one (𝟙 _) := by
    show e.symm ((0 : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) = _
    rw [QuotientAddGroup.mk_zero]; exact equiv_symm_zero L Λ e he
  have hπ'0 : π' 0 = L'.one (𝟙 _) := by
    show e'.symm ((0 : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) = _
    rw [QuotientAddGroup.mk_zero]; exact equiv_symm_zero L' Λ' e' he'
  have key0 : mapPt u hu (π 0) = π' 0 := by
    rw [hπ0, hπ'0]; exact mapPt_one L L' Λ' e' he' u hu hhom

  obtain ⟨δ, hδ, hdisc⟩ := exists_pos_forall_norm_lt_eq_zero Λ' hL1'

  obtain ⟨U', t', ε', D', F', hε', hball', hF', hD'⟩ := hCOV' 0

  have hFdiff : DifferentiableOn ℂ F' (ball (0 : Fin g' → ℂ) ε') := by
    rw [differentiableOn_pi]
    intro i
    obtain ⟨-, Fi, hFi, hFieq⟩ := hAN' U' (t' i)
    refine (hFi.mono fun w hw => hball' w hw).congr fun w hw => ?_
    rw [hF' w (hball' w hw) hw, hFieq w (hball' w hw)]
  have hC1 : ContDiffOn ℂ 1 F' (ball (0 : Fin g' → ℂ) ε') :=
    Complex.contDiffOn_one_of_differentiableOn_pi isOpen_ball hFdiff
  have hstrict : HasStrictFDerivAt F' (D' : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) 0 :=
    (hC1.contDiffAt (isOpen_ball.mem_nhds (mem_ball_self hε'))).hasStrictFDerivAt' hD' one_ne_zero
  set ginv := hstrict.localInverse F' D' 0 with hginv
  have hleft : ∀ᶠ w in 𝓝 (0 : Fin g' → ℂ), ginv (F' w) = w := hstrict.eventually_left_inverse
  have hginv0 : ginv (F' 0) = 0 := hstrict.localInverse_apply_image
  have hginvD : HasFDerivAt ginv (D'.symm : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) (F' 0) :=
    hstrict.to_localInverse.hasFDerivAt

  obtain ⟨ρ₁, hρ₁, hρ₁sub⟩ := Metric.eventually_nhds_iff_ball.mp hleft
  set ρ₀ : ℝ := min (min ρ₁ ε') (δ / 3) with hρ₀
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; exact lt_min (lt_min hρ₁ hε') (by linarith)
  have hρ₀ρ₁ : ρ₀ ≤ ρ₁ := (min_le_left _ _).trans (min_le_left _ _)
  have hρ₀ε : ρ₀ ≤ ε' := (min_le_left _ _).trans (min_le_right _ _)
  have hρ₀δ : ρ₀ ≤ δ / 3 := min_le_right _ _

  have hANu := fun i : Fin g' => (hAN (u ⁻¹ᵁ U') (u.app U' (t' i))).2
  choose C hCd hCeq using hANu
  set S : Set (Fin g → ℂ) := {v | ⊤ ≤ (π v).1 ⁻¹ᵁ (u ⁻¹ᵁ U')} with hS
  have hSopen : IsOpen S := (hAN (u ⁻¹ᵁ U') 0).1
  have hpre : ∀ (v : Fin g → ℂ) (V : G'.Opens), (π v).1 ⁻¹ᵁ (u ⁻¹ᵁ V) = (mapPt u hu (π v)).1 ⁻¹ᵁ V := by
    intro v V; rw [mapPt_coe]; rfl
  have h0S : (0 : Fin g → ℂ) ∈ S := by
    show ⊤ ≤ (π 0).1 ⁻¹ᵁ (u ⁻¹ᵁ U')
    rw [hpre, key0]
    exact hball' 0 (mem_ball_self hε')
  set c : (Fin g → ℂ) → (Fin g' → ℂ) := fun v i => C i v with hc
  have hcd : DifferentiableOn ℂ c S := differentiableOn_pi.mpr fun i => hCd i
  have hcval : ∀ (v : Fin g → ℂ) (hv : v ∈ S) (i : Fin g'),
      c v i = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
        (((mapPt u hu (π v)).1.appLE U' ⊤ (by rw [← hpre]; exact hv)) (t' i)) := by
    intro v hv i
    show C i v = _
    rw [hCeq i v hv]
    exact congrArg _ (appLE_comp_apply u (π v).1 U' (t' i) _).symm

  have hc0 : c 0 = F' 0 := by
    funext i
    rw [hcval 0 h0S i, hF' 0 (hball' 0 (mem_ball_self hε')) (mem_ball_self hε')]
    congr 1
    exact appLE_apply_congr_pt key0 U' (t' i) _ _

  set ℓ : (Fin g → ℂ) → (Fin g' → ℂ) := fun v => ginv (c v) with hℓ
  have hℓ0 : ℓ 0 = 0 := by show ginv (c 0) = 0; rw [hc0]; exact hginv0

  have hkey : ∀ᶠ v in 𝓝 (0 : Fin g → ℂ), H v = ((ℓ v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) ∧ ‖ℓ v‖ < ρ₀ := by
    obtain ⟨U₁, fs, ε₁, h₀, hε₁, hsurj⟩ := hSURJ' 0 ρ₀ hρ₀pos

    set S₁ : Set (Fin g → ℂ) := {v | ⊤ ≤ (π v).1 ⁻¹ᵁ (u ⁻¹ᵁ U₁)} with hS₁
    have hS₁open : IsOpen S₁ := (hAN (u ⁻¹ᵁ U₁) 0).1
    have h0S₁ : (0 : Fin g → ℂ) ∈ S₁ := by
      show ⊤ ≤ (π 0).1 ⁻¹ᵁ (u ⁻¹ᵁ U₁)
      rw [hpre, key0]
      exact h₀
    have hev₁ : ∀ᶠ v in 𝓝 (0 : Fin g → ℂ), v ∈ S₁ := hS₁open.mem_nhds h0S₁
    have hev₂ : ∀ᶠ v in 𝓝 (0 : Fin g → ℂ), v ∈ S := hSopen.mem_nhds h0S
    have hev₃ : ∀ φ ∈ fs, ∀ᶠ v in 𝓝 (0 : Fin g → ℂ), ∀ (hv : v ∈ S₁),
        ‖(Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((mapPt u hu (π v)).1.appLE U₁ ⊤ (by rw [← hpre]; exact hv)) φ) -
          (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom (((e'.symm ((0 : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U₁ ⊤ h₀) φ)‖ < ε₁ := by
      intro φ _
      obtain ⟨-, Cφ, hCφd, hCφeq⟩ := hAN (u ⁻¹ᵁ U₁) (u.app U₁ φ)
      have hcont : ContinuousAt Cφ 0 := (hCφd.continuousOn.continuousAt (hS₁open.mem_nhds h0S₁))
      have hval : ∀ (v : Fin g → ℂ) (hv : v ∈ S₁), Cφ v = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((mapPt u hu (π v)).1.appLE U₁ ⊤ (by rw [← hpre]; exact hv)) φ) := by
        intro v hv
        rw [hCφeq v hv]
        exact congrArg _ (appLE_comp_apply u (π v).1 U₁ φ _).symm
      have h0val : Cφ 0 = (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom
          (((e'.symm ((0 : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup)).1.appLE U₁ ⊤ h₀) φ) := by
        rw [hval 0 h0S₁]; congr 1
        exact appLE_apply_congr_pt key0 U₁ φ _ _
      have := (hcont.tendsto).eventually (Metric.ball_mem_nhds (Cφ 0) hε₁)
      filter_upwards [this] with v hv hvS
      rw [← hval v hvS, ← h0val, ← dist_eq_norm]
      exact hv
    have hev₃' := (Filter.eventually_all_finset fs).mpr hev₃
    filter_upwards [hev₁, hev₂, hev₃'] with v hv₁ hv₂ hv₃
    have hP : ⊤ ≤ (mapPt u hu (π v)).1 ⁻¹ᵁ U₁ := by rw [← hpre]; exact hv₁
    obtain ⟨w, hw, hew⟩ := hsurj (mapPt u hu (π v)) hP (fun φ hφ => hv₃ φ hφ hv₁)

    have hπ'w : π' w = mapPt u hu (π v) := by
      show e'.symm (w : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) = _
      rw [Equiv.symm_apply_eq]; exact hew.symm
    have hwε : w ∈ ball (0 : Fin g' → ℂ) ε' := Metric.ball_subset_ball hρ₀ε hw
    have hFw : F' w = c v := by
      rw [hF' w (hball' w hwε) hwε]
      funext i
      rw [hcval v hv₂ i]
      congr 1
      exact appLE_apply_congr_pt hπ'w U' (t' i) _ _
    have hwℓ : w = ℓ v := by
      show w = ginv (c v)
      rw [← hFw]; exact (hρ₁sub w (Metric.ball_subset_ball hρ₀ρ₁ hw)).symm
    refine ⟨?_, ?_⟩
    · rw [hHv, hew, hwℓ]
    · rw [← hwℓ]; rwa [mem_ball, dist_zero_right] at hw

  obtain ⟨ρ, hρ, hρsub⟩ := Metric.eventually_nhds_iff_ball.mp hkey

  have hadd : ∀ v w : Fin g → ℂ, ‖v‖ < ρ → ‖w‖ < ρ → ‖v + w‖ < ρ → ℓ (v + w) = ℓ v + ℓ w := by
    intro v w hv hw hvw
    have kv := hρsub v (by rwa [mem_ball, dist_zero_right])
    have kw := hρsub w (by rwa [mem_ball, dist_zero_right])
    have kvw := hρsub (v + w) (by rwa [mem_ball, dist_zero_right])
    have hmem : ℓ (v + w) - (ℓ v + ℓ w) ∈ Λ' := by
      rw [← Submodule.mem_toAddSubgroup, ← QuotientAddGroup.eq_iff_sub_mem, QuotientAddGroup.mk_add]
      rw [← kvw.1, ← kv.1, ← kw.1, map_add]
    have hsmall : ‖ℓ (v + w) - (ℓ v + ℓ w)‖ < δ := by
      calc ‖ℓ (v + w) - (ℓ v + ℓ w)‖ ≤ ‖ℓ (v + w)‖ + ‖ℓ v + ℓ w‖ := norm_sub_le _ _
        _ ≤ ‖ℓ (v + w)‖ + (‖ℓ v‖ + ‖ℓ w‖) := by gcongr; exact norm_add_le _ _
        _ < ρ₀ + (ρ₀ + ρ₀) := by gcongr; exacts [kvw.2, kv.2, kw.2]
        _ ≤ δ := by linarith
    exact sub_eq_zero.mp (hdisc _ hmem hsmall)

  have hcAt : HasFDerivAt c (fderiv ℂ c 0) 0 :=
    ((hcd 0 h0S).differentiableAt (hSopen.mem_nhds h0S)).hasFDerivAt
  have hginvD' : HasFDerivAt ginv (D'.symm : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)) (c 0) := by rw [hc0]; exact hginvD
  have hℓD : HasFDerivAt ℓ ((D'.symm : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)).comp (fderiv ℂ c 0)) 0 :=
    hginvD'.comp 0 hcAt
  set T : (Fin g → ℂ) →L[ℂ] (Fin g' → ℂ) := (D'.symm : (Fin g' → ℂ) →L[ℂ] (Fin g' → ℂ)).comp (fderiv ℂ c 0) with hT
  have hlin : ∀ v : Fin g → ℂ, ‖v‖ < ρ → ℓ v = T v := eq_fderiv_of_locally_additive hρ hadd hℓD

  have hHT : ∀ v : Fin g → ℂ, H v = ((T v : Fin g' → ℂ) : (Fin g' → ℂ) ⧸ Λ'.toAddSubgroup) := by
    refine forall_eq_mk_of_eqOn_ball Λ' H T.toLinearMap hρ fun v hv => ?_
    rw [(hρsub v (by rwa [mem_ball, dist_zero_right])).1, hlin v hv]
    rfl

  refine ⟨T.toLinearMap, ⟨fun v hv => ?_, fun P v hPv => ?_⟩, fun T₂ hT₂ => ?_⟩
  ·
    have h1 : H v = H 0 := by
      show e' (mapPt u hu (π v)) = e' (mapPt u hu (π 0))
      have : (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) = ((0 : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ.toAddSubgroup) := by
        rw [QuotientAddGroup.mk_zero, QuotientAddGroup.eq_zero_iff]; exact hv
      show e' (mapPt u hu (e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup))) = e' (mapPt u hu (e.symm ((0 : Fin g → ℂ) : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)))
      rw [this]
    rw [map_zero, hHT] at h1
    rw [← Submodule.mem_toAddSubgroup, ← QuotientAddGroup.eq_zero_iff]
    exact h1
  ·
    have hP : P = π v := by
      show P = e.symm (v : (Fin g → ℂ) ⧸ Λ.toAddSubgroup)
      rw [Equiv.eq_symm_apply]; exact hPv
    rw [hP, ← hHv, hHT]
    rfl
  ·
    refine linearMap_eq_of_forall_sub_mem Λ' hL1' T₂ T.toLinearMap fun v => ?_
    rw [← Submodule.mem_toAddSubgroup, ← QuotientAddGroup.eq_iff_sub_mem]
    have h2 := hT₂.2 (π v) v (by show e (e.symm _) = _; exact Equiv.apply_symm_apply _ _)
    rw [← h2, ← hHv, hHT]
    rfl

end
end S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_existsUnique_linearMap_forall_pointEquiv_mapPt_eq_of_differentiableOn_appLE (solution)
