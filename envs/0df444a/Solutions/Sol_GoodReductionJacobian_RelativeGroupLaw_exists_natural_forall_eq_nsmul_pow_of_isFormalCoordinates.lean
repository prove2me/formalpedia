-- Prove2me | solution 1 for GoodReductionJacobian.RelativeGroupLaw.exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/e7d5c618-35ac-557e-b339-6ba64b5c4b1b

import Mathlib
import Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_nsmul_pow_eq_one_of_isInfinitesimal
import Theorems.Thm_AlgebraicGeometry_Smooth_exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

namespace KatzNTrick

section GroupLaw

variable {B : Type} [CommRing B] {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of B)} (L : RelativeGroupLaw B f)

theorem nsmul_eq_pow {T : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (n : ℕ) (x : SchemeHomOver t f) :
    L.nsmul t n x = (letI := L.pointGroup t; x ^ n) := by
  letI := L.pointGroup t
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [RelativeGroupLaw.nsmul_succ, ih, pow_succ]
      rfl

theorem inv_natural {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (t' : T' ⟶ Spec (CommRingCat.of B))
    (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    schemeHomOverComp ψ hψ (L.inv t x) = L.inv t' (schemeHomOverComp ψ hψ x) := by
  letI := L.pointGroup t'
  have h : L.mul t' (schemeHomOverComp ψ hψ (L.inv t x)) (schemeHomOverComp ψ hψ x) = L.one t' := by
    rw [← L.mul_natural, L.inv_mul_cancel, L.one_natural]
  have h' : (schemeHomOverComp ψ hψ (L.inv t x)) * (schemeHomOverComp ψ hψ x) = 1 := h
  exact eq_inv_of_mul_eq_one_left h'

theorem nsmul_val_congr {T : Scheme.{0}} {t t' : T ⟶ Spec (CommRingCat.of B)} (e : t = t') {n : ℕ}
    {y : T ⟶ A} {hy : y ≫ f = t} :
    (L.nsmul t n ⟨y, hy⟩).1 = (L.nsmul t' n ⟨y, hy.trans e⟩).1 := by
  subst e; rfl

theorem nsmul_val_congr' {T : Scheme.{0}} {t : T ⟶ Spec (CommRingCat.of B)} (n : ℕ)
    (y y' : SchemeHomOver t f) (e : y.1 = y'.1) :
    (L.nsmul t n y).1 = (L.nsmul t n y').1 := by
  have : y = y' := Subtype.ext e
  subst this; rfl

theorem comp_nsmul_val {T T' : Scheme.{0}} (t : T ⟶ Spec (CommRingCat.of B)) (w : T' ⟶ T) (n : ℕ)
    (y : SchemeHomOver t f) :
    w ≫ (L.nsmul t n y).1 = (L.nsmul (w ≫ t) n ⟨w ≫ y.1, by rw [Category.assoc, y.2]⟩).1 := by
  have := L.nsmul_natural t (w ≫ t) w rfl n y
  have h := congrArg Subtype.val this
  rw [schemeHomOverComp_coe] at h
  rw [h]
  rfl

theorem key (hc : L.IsCommutative) {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f d)
    (hθ : L.IsFormalCoordinates F θ) (N : ℕ) (hN : (N : B) = 0) (μ : ℕ)
    (D : Type) [CommRing D] [Algebra B D] (J : Ideal D) (hJ : J ^ (μ + 1) = ⊥)
    (y y' : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B D))) f)
    (hyy' : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ y.1 =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)) ≫ y'.1) :
    (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B D))) (N ^ μ) y).1 =
      (L.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B D))) (N ^ μ) y').1 := by

  letI inst : CommGroup (SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B D))) f) :=
    { L.pointGroup _ with mul_comm := fun a b => hc.mul_comm _ a b }
  have hND : (N : D) = 0 := by
    rw [← map_natCast (algebraMap B D) N, hN, map_zero]

  set δ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap B D))) f := y * y'⁻¹ with hδ
  have hred : schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
      (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y =
      schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
      (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y' := by
    apply Subtype.ext
    simp only [schemeHomOverComp_coe]
    exact hyy'
  have hinf : L.IsInfinitesimal J δ := by
    unfold RelativeGroupLaw.IsInfinitesimal
    letI instq := L.pointGroup (Scheme.specOver (𝒪 := B) (D ⧸ J))
    have e1 : schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
        (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) δ =
        L.mul _ (schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
          (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y)
        (L.inv _ (schemeHomOverComp (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mkₐ B J).toRingHom))
          (Scheme.specMap_algHom_comp_specOver (Ideal.Quotient.mkₐ B J)) y')) := by
      rw [hδ]
      show schemeHomOverComp _ _ (L.mul _ y (L.inv _ y')) = _
      rw [L.mul_natural, inv_natural]
    rw [e1, hred]
    exact L.mul_inv_cancel _ _
  have hkill := GoodReductionJacobian.RelativeGroupLaw.nsmul_pow_eq_one_of_isInfinitesimal L F θ hθ N hND J μ hJ δ hinf

  have hk : δ ^ (N ^ μ) = 1 := by
    have := (nsmul_eq_pow L _ (N ^ μ) δ).symm.trans hkill
    exact this
  have hy : y = δ * y' := by rw [hδ, inv_mul_cancel_right]
  congr 1
  rw [nsmul_eq_pow, nsmul_eq_pow]
  show y ^ (N ^ μ) = y' ^ (N ^ μ)
  rw [hy, mul_pow, hk, one_mul]

end GroupLaw

section Plumbing

theorem red_comp {E D : Type} [CommRing E] [CommRing D] (ρ : E →+* D) (JE : Ideal E) (JD : Ideal D)
    (hle : JE ≤ JD.comap ρ) {T : Scheme.{0}} (y : Spec (CommRingCat.of E) ⟶ T)
    (z : Spec (CommRingCat.of (E ⧸ JE)) ⟶ T) (hy : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ y = z) :
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JD)) ≫ (Spec.map (CommRingCat.ofHom ρ) ≫ y) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap JD ρ hle)) ≫ z := by
  rw [← hy, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
    ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

theorem specMap_cancel_of_surjective {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀)) {E : Type} [CommRing E]
    (σ σ' : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of B₀))
    (h : σ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)) = σ' ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :
    σ = σ' := by
  rw [← Spec.map_preimage σ, ← Spec.map_preimage σ'] at h ⊢
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
  congr 1
  ext x
  obtain ⟨b, rfl⟩ := hπ x
  have := congrArg (fun χ => (CommRingCat.Hom.hom χ) b) h
  simpa only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] using this

theorem fold {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : S →+* T) (b : R →+* S) :
    Spec.map (CommRingCat.ofHom a) ≫ Spec.map (CommRingCat.ofHom b) = Spec.map (CommRingCat.ofHom (a.comp b)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem fold_assoc {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (a : S →+* T) (b : R →+* S)
    {X : Scheme.{0}} (h : Spec (CommRingCat.of R) ⟶ X) :
    Spec.map (CommRingCat.ofHom a) ≫ (Spec.map (CommRingCat.ofHom b) ≫ h) =
      Spec.map (CommRingCat.ofHom (a.comp b)) ≫ h := by
  rw [← Category.assoc, fold]

end Plumbing

section Engine

variable {B : Type} [CommRing B] {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} (L' : RelativeGroupLaw B f')

theorem specMap_ofHom_preimage {R S : Type} [CommRing R] [CommRing S]
    (w : Spec (CommRingCat.of S) ⟶ Spec (CommRingCat.of R)) :
    Spec.map (CommRingCat.ofHom (Spec.preimage w).hom) = w := by
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

theorem ringHom_eq_of_specMap_eq {R S : Type} [CommRing R] [CommRing S] (φ ψ : R →+* S)
    (h : Spec.map (CommRingCat.ofHom φ) = Spec.map (CommRingCat.ofHom ψ)) : φ = ψ := by
  have h2 := Spec.map_inj.mp h
  have h3 := congrArg CommRingCat.Hom.hom h2
  simpa only [CommRingCat.hom_ofHom] using h3

theorem engine (hc : L'.IsCommutative) {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f' d)
    (hθ : L'.IsFormalCoordinates F θ) (N : ℕ) (hN : (N : B) = 0) (μ : ℕ)
    {C : Type} [CommRing C] (tC : Spec (CommRingCat.of C) ⟶ Spec (CommRingCat.of B)) (JC : Ideal C)
    (x0 : Spec (CommRingCat.of (C ⧸ JC)) ⟶ A')
    (a : C) (xa : Spec (CommRingCat.of (Localization.Away a)) ⟶ A')
    (hxa : xa ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC)
    (hreda : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JC.map (algebraMap C (Localization.Away a))))) ≫ xa =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (JC.map (algebraMap C (Localization.Away a)))
        (algebraMap C (Localization.Away a)) Ideal.le_comap_map)) ≫ x0)
    {E : Type} [CommRing E] (tE : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of C))
    (y : Spec (CommRingCat.of E) ⟶ A') (hy : y ≫ f' = tE ≫ tC) (JE : Ideal E) (hJE : JE ^ (μ + 1) = ⊥)
    (q : C ⧸ JC →+* E ⧸ JE)
    (hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ tE =
      Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JC)))
    (hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ y = Spec.map (CommRingCat.ofHom q) ≫ x0)
    {D : Type} [CommRing D] (w : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of (Localization.Away a)))
    (u : Spec (CommRingCat.of D) ⟶ Spec (CommRingCat.of E))
    (hwu : w ≫ Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) = u ≫ tE) :
    w ≫ (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC) (N ^ μ) ⟨xa, hxa⟩).1 =
      u ≫ (L'.nsmul (tE ≫ tC) (N ^ μ) ⟨y, hy⟩).1 := by
  classical

  obtain ⟨ρw, hw⟩ : ∃ ρ : Localization.Away a →+* D, Spec.map (CommRingCat.ofHom ρ) = w :=
    ⟨_, specMap_ofHom_preimage w⟩
  obtain ⟨ρu, hu⟩ : ∃ ρ : E →+* D, Spec.map (CommRingCat.ofHom ρ) = u := ⟨_, specMap_ofHom_preimage u⟩
  obtain ⟨αE, htE⟩ : ∃ ρ : C →+* E, Spec.map (CommRingCat.ofHom ρ) = tE := ⟨_, specMap_ofHom_preimage tE⟩

  have hχ : ρw.comp (algebraMap C (Localization.Away a)) = ρu.comp αE := by
    apply ringHom_eq_of_specMap_eq
    conv_lhs => rw [CommRingCat.ofHom_comp, Spec.map_comp, hw]
    conv_rhs => rw [CommRingCat.ofHom_comp, Spec.map_comp, hu, htE]
    exact hwu

  have hqE : (Ideal.Quotient.mk JE).comp αE = q.comp (Ideal.Quotient.mk JC) := by
    apply ringHom_eq_of_specMap_eq
    conv_lhs => rw [CommRingCat.ofHom_comp, Spec.map_comp, htE]
    conv_rhs => rw [CommRingCat.ofHom_comp, Spec.map_comp]
    exact hq
  have hJCE : JC.map αE ≤ JE := by
    rw [Ideal.map_le_iff_le_comap]
    intro c hcJ
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, ← RingHom.comp_apply, hqE, RingHom.comp_apply,
      Ideal.Quotient.eq_zero_iff_mem.mpr hcJ, map_zero]

  obtain ⟨β, hβ⟩ : ∃ β : B →+* D, Spec.map (CommRingCat.ofHom β) =
      w ≫ (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC) :=
    ⟨_, specMap_ofHom_preimage _⟩
  letI : Algebra B D := β.toAlgebra
  have hbase : w ≫ (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away a))) ≫ tC) =
      Spec.map (CommRingCat.ofHom (algebraMap B D)) := hβ.symm
  have hbase' : u ≫ (tE ≫ tC) = Spec.map (CommRingCat.ofHom (algebraMap B D)) := by
    rw [← hbase, ← Category.assoc, ← Category.assoc, ← hwu]
  rw [comp_nsmul_val, comp_nsmul_val, nsmul_val_congr L' hbase, nsmul_val_congr L' hbase']
  have hJ : JE.map ρu ^ (μ + 1) = ⊥ := by rw [← Ideal.map_pow, hJE, Ideal.map_bot]
  refine key L' hc F θ hθ N hN μ D (JE.map ρu) hJ _ _ ?_

  show Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JE.map ρu))) ≫ (w ≫ xa) =
    Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JE.map ρu))) ≫ (u ≫ y)
  have hle_w : JC.map (algebraMap C (Localization.Away a)) ≤ (JE.map ρu).comap ρw := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_map, hχ, ← Ideal.map_map]
    exact Ideal.map_mono hJCE
  have hle_u : JE ≤ (JE.map ρu).comap ρu := Ideal.le_comap_map
  rw [← hw, ← hu, red_comp ρw _ _ hle_w xa _ hreda, red_comp ρu _ _ hle_u y _ hred, ← Category.assoc,
    ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  have hr : (Ideal.quotientMap (JE.map ρu) ρw hle_w).comp
        (Ideal.quotientMap (JC.map (algebraMap C (Localization.Away a))) (algebraMap C (Localization.Away a))
          Ideal.le_comap_map) =
      (Ideal.quotientMap (JE.map ρu) ρu hle_u).comp q := by
    apply Ideal.Quotient.ringHom_ext
    apply RingHom.ext
    intro c
    have hqc : q (Ideal.Quotient.mk JC c) = Ideal.Quotient.mk JE (αE c) := by
      have := congrArg (fun χ : C →+* E ⧸ JE => χ c) hqE
      simpa only [RingHom.comp_apply] using this.symm
    simp only [RingHom.comp_apply, Ideal.quotientMap_mk, hqc]
    have := congrArg (fun χ : C →+* D => χ c) hχ
    simp only [RingHom.comp_apply] at this
    rw [this]
  rw [hr]

end Engine

section Main

variable {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
  (hπ : Function.Surjective (algebraMap B B₀))
  (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (N : ℕ) (hN : (N : B) = 0)
  {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} [Smooth f'] (L' : RelativeGroupLaw B f')
  (hc : L'.IsCommutative) {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f' d)
  (hθ : L'.IsFormalCoordinates F θ)
  {Z Z₀ : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of B)) (fZ₀ : Z₀ ⟶ Spec (CommRingCat.of B₀)) (g : Z₀ ⟶ Z)
  (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
  (ψ : Z₀ ⟶ A') (hψ : ψ ≫ f' = fZ₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀)))

abbrev JJ (B B₀ : Type) [CommRing B] [CommRing B₀] [Algebra B B₀] (C : Type) [CommRing C] [Algebra B C] : Ideal C :=
  (RingHom.ker (algebraMap B B₀)).map (algebraMap B C)

include hμ in
theorem JJ_pow (C : Type) [CommRing C] [Algebra B C] : JJ B B₀ C ^ (μ + 1) = ⊥ := by
  rw [JJ, ← Ideal.map_pow, hμ, Ideal.map_bot]

noncomputable def toQuot (C : Type) [CommRing C] [Algebra B C] : B₀ →+* C ⧸ JJ B B₀ C :=
  (algebraMap B B₀).liftOfSurjective hπ
    ⟨(Ideal.Quotient.mk (JJ B B₀ C)).comp (algebraMap B C), fun b hb => by
      rw [RingHom.mem_ker, RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_map_of_mem _ hb⟩

theorem toQuot_comp (C : Type) [CommRing C] [Algebra B C] :
    (toQuot hπ C).comp (algebraMap B B₀) = (Ideal.Quotient.mk (JJ B B₀ C)).comp (algebraMap B C) :=
  RingHom.liftOfSurjective_comp _ _ _

noncomputable def red₀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ Z₀ :=
  hg.lift (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ P)
    (Spec.map (CommRingCat.ofHom (toQuot hπ C))) (by
      rw [Category.assoc, hP, ← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
        toQuot_comp])

theorem red₀_fst (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    red₀ hπ fZ fZ₀ g hg C P hP ≫ g = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ P :=
  hg.lift_fst _ _ _

theorem red₀_snd (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    red₀ hπ fZ fZ₀ g hg C P hP ≫ fZ₀ = Spec.map (CommRingCat.ofHom (toQuot hπ C)) :=
  hg.lift_snd _ _ _

include hπ in

theorem hom_ext_Z₀ (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    {E : Type} [CommRing E] (Q Q' : Spec (CommRingCat.of E) ⟶ Z₀) (h : Q ≫ g = Q' ≫ g) :
    Q = Q' := by
  apply hg.hom_ext h
  apply specMap_cancel_of_surjective hπ
  rw [Category.assoc, Category.assoc, ← hg.w, ← Category.assoc, h, Category.assoc]

noncomputable def x₀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ A' :=
  red₀ hπ fZ fZ₀ g hg C P hP ≫ ψ

include hψ in
theorem x₀_over (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
    (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    x₀ hπ fZ fZ₀ g hg ψ C P hP ≫ f' =
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
  rw [x₀, Category.assoc, hψ, ← Category.assoc, red₀_snd, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, toQuot_comp]

include hπ in

theorem x₀_nat (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C'] (φ : C →+* C')
    (P : Spec (CommRingCat.of C) ⟶ Z) (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
    (hP' : (Spec.map (CommRingCat.ofHom φ) ≫ P) ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C')))
    (hle : JJ B B₀ C ≤ (JJ B B₀ C').comap φ) :
    x₀ hπ fZ fZ₀ g hg ψ C' (Spec.map (CommRingCat.ofHom φ) ≫ P) hP' =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap (JJ B B₀ C') φ hle)) ≫ x₀ hπ fZ fZ₀ g hg ψ C P hP := by
  unfold x₀
  rw [← Category.assoc]
  congr 1
  apply hom_ext_Z₀ hπ fZ fZ₀ g hg
  rw [red₀_fst, Category.assoc, red₀_fst, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, Ideal.quotientMap_comp_mk]

end Main

structure LiftCover {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀] {A' : Scheme.{0}}
    (f' : A' ⟶ Spec (CommRingCat.of B)) (C : Type) [CommRing C] [Algebra B C]
    (z : Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ A') where
  ι : Type
  a : ι → C
  hspan : Ideal.span (Set.range a) = ⊤
  x : ∀ i, Spec (CommRingCat.of (Localization.Away (a i))) ⟶ A'
  hx : ∀ i, x i ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away (a i)))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap B C))
  hred : ∀ i, Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((JJ B B₀ C).map (algebraMap C (Localization.Away (a i)))))) ≫ x i =
    Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((JJ B B₀ C).map (algebraMap C (Localization.Away (a i))))
      (algebraMap C (Localization.Away (a i))) Ideal.le_comap_map)) ≫ z

theorem nonempty_liftCover {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥)
    {A' : Scheme.{0}} (f' : A' ⟶ Spec (CommRingCat.of B)) [Smooth f'] (C : Type) [CommRing C] [Algebra B C]
    (z : Spec (CommRingCat.of (C ⧸ JJ B B₀ C)) ⟶ A')
    (hz : z ≫ f' = Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫
      Spec.map (CommRingCat.ofHom (algebraMap B C))) :
    Nonempty (LiftCover f' C z) := by
  have hnil : IsNilpotent (JJ B B₀ C) := ⟨μ + 1, by rw [JJ_pow μ hμ C]; exact Submodule.zero_eq_bot.symm⟩
  obtain ⟨ι, a, hspan, h⟩ :=
    AlgebraicGeometry.Smooth.exists_span_eq_top_and_forall_exists_lift_away_of_isNilpotent f' (JJ B B₀ C) hnil
      (Spec.map (CommRingCat.ofHom (algebraMap B C))) z hz
  choose x hx hred using h
  exact ⟨⟨ι, a, hspan, x, hx, hred⟩⟩

end KatzNTrick

open KatzNTrick in
theorem solution
    {B B₀ : Type} [CommRing B] [CommRing B₀] [Algebra B B₀]
    (hπ : Function.Surjective (algebraMap B B₀))
    (μ : ℕ) (hμ : RingHom.ker (algebraMap B B₀) ^ (μ + 1) = ⊥) (N : ℕ) (hN : (N : B) = 0)
    {A' : Scheme.{0}} {f' : A' ⟶ Spec (CommRingCat.of B)} [Smooth f'] (L' : RelativeGroupLaw B f')
    (hc : L'.IsCommutative) {d : ℕ} (F : MvFormalGroup d B) (θ : RelativeGroupLaw.FormalCoordinates f' d)
    (hθ : L'.IsFormalCoordinates F θ)
    {Z Z₀ : Scheme.{0}} (fZ : Z ⟶ Spec (CommRingCat.of B)) (fZ₀ : Z₀ ⟶ Spec (CommRingCat.of B₀)) (g : Z₀ ⟶ Z)
    (hg : CategoryTheory.IsPullback g fZ₀ fZ (Spec.map (CommRingCat.ofHom (algebraMap B B₀))))
    (ψ : Z₀ ⟶ A') (hψ : ψ ≫ f' = fZ₀ ≫ Spec.map (CommRingCat.ofHom (algebraMap B B₀))) :
    ∃ Ñ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z),
        P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)) → (Spec (CommRingCat.of C) ⟶ A'),
      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))),
        Ñ C P hP ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C))) ∧
      (∀ (C C' : Type) [CommRing C] [Algebra B C] [CommRing C'] [Algebra B C'] (φ : C →ₐ[B] C')
        (P : Spec (CommRingCat.of C) ⟶ Z) (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hP' : (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) ≫ fZ =
          Spec.map (CommRingCat.ofHom (algebraMap B C'))),
        Ñ C' (Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P) hP' =
          Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ Ñ C P hP) ∧
      (∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
        (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (P₀ : Spec (CommRingCat.of (C ⧸ (RingHom.ker (algebraMap B B₀)).map (algebraMap B C))) ⟶ Z₀)
        (hP₀ : P₀ ≫ g =
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ P)
        (x : Spec (CommRingCat.of C) ⟶ A') (hx : x ≫ f' = Spec.map (CommRingCat.ofHom (algebraMap B C)))
        (hlift : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((RingHom.ker (algebraMap B B₀)).map (algebraMap B C)))) ≫ x =
          P₀ ≫ ψ),
        Ñ C P hP = (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨x, hx⟩).1) := by
  classical

  let Λ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))),
      LiftCover (B₀ := B₀) f' C (x₀ hπ fZ fZ₀ g hg ψ C P hP) :=
    fun C _ _ P hP => Classical.choice (nonempty_liftCover μ hμ f' C _ (x₀_over hπ fZ fZ₀ g hg ψ hψ C P hP))

  let 𝒰 : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))), (Spec (CommRingCat.of C)).OpenCover :=
    fun C _ _ P hP =>
      (Scheme.affineOpenCoverOfSpanRangeEqTop (R := CommRingCat.of C) (Λ C P hP).a (Λ C P hP).hspan).openCover
  let v : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) (i : (Λ C P hP).ι),
      Spec (CommRingCat.of (Localization.Away ((Λ C P hP).a i))) ⟶ A' :=
    fun C _ _ P hP i =>
      (L'.nsmul (Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away ((Λ C P hP).a i)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨(Λ C P hP).x i, (Λ C P hP).hx i⟩).1

  have hJi : ∀ (C : Type) [CommRing C] [Algebra B C] (c : C),
      (JJ B B₀ C).map (algebraMap C (Localization.Away c)) ^ (μ + 1) = ⊥ := by
    intro C _ _ c
    rw [← Ideal.map_pow, JJ_pow μ hμ C, Ideal.map_bot]
  have hqi : ∀ (C : Type) [CommRing C] [Algebra B C] (c : C),
      Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk ((JJ B B₀ C).map (algebraMap C (Localization.Away c))))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away c))) =
      Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((JJ B B₀ C).map (algebraMap C (Localization.Away c)))
        (algebraMap C (Localization.Away c)) Ideal.le_comap_map)) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) := by
    intro C _ _ c
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      Ideal.quotientMap_comp_mk]

  have compat : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) (i j : (Λ C P hP).ι),
      pullback.fst ((𝒰 C P hP).f i) ((𝒰 C P hP).f j) ≫ v C P hP i =
        pullback.snd ((𝒰 C P hP).f i) ((𝒰 C P hP).f j) ≫ v C P hP j := by
    intro C _ _ P hP i j
    let 𝒱 := (pullback ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)).affineOpenCover
    refine 𝒱.openCover.hom_ext _ _ fun k => ?_
    change (𝒱.f k ≫ pullback.fst ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ v C P hP i =
      (𝒱.f k ≫ pullback.snd ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ v C P hP j
    have hwu : (𝒱.f k ≫ pullback.fst ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ (𝒰 C P hP).f i =
        (𝒱.f k ≫ pullback.snd ((𝒰 C P hP).f i) ((𝒰 C P hP).f j)) ≫ (𝒰 C P hP).f j := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    exact engine L' hc F θ hθ N hN μ (Spec.map (CommRingCat.ofHom (algebraMap B C))) (JJ B B₀ C)
      (x₀ hπ fZ fZ₀ g hg ψ C P hP) ((Λ C P hP).a i) ((Λ C P hP).x i) ((Λ C P hP).hx i) ((Λ C P hP).hred i)
      ((𝒰 C P hP).f j) ((Λ C P hP).x j) ((Λ C P hP).hx j)
      ((JJ B B₀ C).map (algebraMap C (Localization.Away ((Λ C P hP).a j)))) (hJi C _)
      (Ideal.quotientMap _ (algebraMap C _) Ideal.le_comap_map) (hqi C _) ((Λ C P hP).hred j)
      (𝒱.f k ≫ pullback.fst _ _) (𝒱.f k ≫ pullback.snd _ _) hwu

  let Ñ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z),
      P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C)) → (Spec (CommRingCat.of C) ⟶ A') :=
    fun C _ _ P hP => (𝒰 C P hP).glueMorphisms (v C P hP) (compat C P hP)
  have hÑ : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) (i : (Λ C P hP).ι),
      (𝒰 C P hP).f i ≫ Ñ C P hP = v C P hP i :=
    fun C _ _ P hP i => (𝒰 C P hP).ι_glueMorphisms _ _ i

  have det : ∀ (C : Type) [CommRing C] [Algebra B C] (P : Spec (CommRingCat.of C) ⟶ Z)
      (hP : P ≫ fZ = Spec.map (CommRingCat.ofHom (algebraMap B C))) {E : Type} [CommRing E]
      (tE : Spec (CommRingCat.of E) ⟶ Spec (CommRingCat.of C)) (y : Spec (CommRingCat.of E) ⟶ A')
      (hy : y ≫ f' = tE ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (JE : Ideal E) (hJE : JE ^ (μ + 1) = ⊥)
      (q : C ⧸ JJ B B₀ C →+* E ⧸ JE)
      (hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ tE =
        Spec.map (CommRingCat.ofHom q) ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))))
      (hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk JE)) ≫ y =
        Spec.map (CommRingCat.ofHom q) ≫ x₀ hπ fZ fZ₀ g hg ψ C P hP),
      tE ≫ Ñ C P hP = (L'.nsmul (tE ≫ Spec.map (CommRingCat.ofHom (algebraMap B C))) (N ^ μ) ⟨y, hy⟩).1 := by
    intro C _ _ P hP E _ tE y hy JE hJE q hq hred
    refine Scheme.Cover.hom_ext ((𝒰 C P hP).pullback₁ tE) _ _ fun i => ?_
    change pullback.fst tE ((𝒰 C P hP).f i) ≫ tE ≫ Ñ C P hP =
      pullback.fst tE ((𝒰 C P hP).f i) ≫ (L'.nsmul _ (N ^ μ) ⟨y, hy⟩).1
    let 𝒲 := (pullback tE ((𝒰 C P hP).f i)).affineOpenCover
    refine 𝒲.openCover.hom_ext _ _ fun k => ?_
    change 𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i) ≫ tE ≫ Ñ C P hP =
      𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i) ≫ (L'.nsmul _ (N ^ μ) ⟨y, hy⟩).1
    have hcond : (𝒲.f k ≫ pullback.snd tE ((𝒰 C P hP).f i)) ≫ (𝒰 C P hP).f i =
        (𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i)) ≫ tE := by
      rw [Category.assoc, Category.assoc, pullback.condition]
    have e1 : 𝒲.f k ≫ pullback.fst tE ((𝒰 C P hP).f i) ≫ tE ≫ Ñ C P hP =
        (𝒲.f k ≫ pullback.snd tE ((𝒰 C P hP).f i)) ≫ v C P hP i := by
      rw [← hÑ C P hP i, Category.assoc, ← Category.assoc (pullback.snd _ _), ← pullback.condition,
        Category.assoc]
    rw [e1, ← Category.assoc (𝒲.f k)]
    exact engine L' hc F θ hθ N hN μ _ (JJ B B₀ C) (x₀ hπ fZ fZ₀ g hg ψ C P hP) ((Λ C P hP).a i)
      ((Λ C P hP).x i) ((Λ C P hP).hx i) ((Λ C P hP).hred i) tE y hy JE hJE q hq hred _ _ hcond
  refine ⟨Ñ, ?_, ?_, ?_⟩
  ·
    intro C _ _ P hP
    refine (𝒰 C P hP).hom_ext _ _ fun i => ?_
    rw [← Category.assoc, hÑ]
    exact (L'.nsmul _ (N ^ μ) ⟨(Λ C P hP).x i, (Λ C P hP).hx i⟩).2
  ·
    intro C C' _ _ _ _ φ P hP hP'
    refine (𝒰 C' _ hP').hom_ext _ _ fun k => ?_
    rw [hÑ, ← Category.assoc]
    have hφ : φ.toRingHom.comp (algebraMap B C) = algebraMap B C' := φ.comp_algebraMap
    have hle : JJ B B₀ C ≤ (JJ B B₀ C').comap φ.toRingHom := by
      rw [← Ideal.map_le_iff_le_comap, JJ, Ideal.map_map, hφ]

    change _ = (Spec.map (CommRingCat.ofHom (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))) ≫
      Spec.map (CommRingCat.ofHom φ.toRingHom)) ≫ Ñ C P hP
    rw [fold]
    have hbase : Spec.map (CommRingCat.ofHom (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))) ≫
        Spec.map (CommRingCat.ofHom (algebraMap B C')) =
        Spec.map (CommRingCat.ofHom ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [fold, fold, RingHom.comp_assoc, hφ]
    have hy : (Λ C' _ hP').x k ≫ f' =
        Spec.map (CommRingCat.ofHom ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom)) ≫
          Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [← hbase]; exact (Λ C' _ hP').hx k
    have hring : (Ideal.Quotient.mk ((JJ B B₀ C').map (algebraMap C' (Localization.Away ((Λ C' _ hP').a k))))).comp
          ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom) =
        ((Ideal.quotientMap _ (algebraMap C' (Localization.Away ((Λ C' _ hP').a k))) Ideal.le_comap_map).comp
          (Ideal.quotientMap (JJ B B₀ C') φ.toRingHom hle)).comp (Ideal.Quotient.mk (JJ B B₀ C)) := by
      ext c
      simp only [RingHom.comp_apply, Ideal.quotientMap_mk]
    have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          ((JJ B B₀ C').map (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))))) ≫
        Spec.map (CommRingCat.ofHom ((algebraMap C' (Localization.Away ((Λ C' _ hP').a k))).comp φ.toRingHom)) =
        Spec.map (CommRingCat.ofHom ((Ideal.quotientMap _ (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))
          Ideal.le_comap_map).comp (Ideal.quotientMap (JJ B B₀ C') φ.toRingHom hle))) ≫
        Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) := by
      rw [fold, fold, hring]
    have hx₀ := x₀_nat hπ fZ fZ₀ g hg ψ C C' φ.toRingHom P hP hP' hle
    have hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk
          ((JJ B B₀ C').map (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))))) ≫ (Λ C' _ hP').x k =
        Spec.map (CommRingCat.ofHom ((Ideal.quotientMap _ (algebraMap C' (Localization.Away ((Λ C' _ hP').a k)))
          Ideal.le_comap_map).comp (Ideal.quotientMap (JJ B B₀ C') φ.toRingHom hle))) ≫
        x₀ hπ fZ fZ₀ g hg ψ C P hP := by
      refine ((Λ C' _ hP').hred k).trans ?_
      refine (congrArg (fun t => Spec.map (CommRingCat.ofHom (Ideal.quotientMap _
        (algebraMap C' (Localization.Away ((Λ C' _ hP').a k))) Ideal.le_comap_map)) ≫ t) hx₀).trans ?_
      exact fold_assoc _ _ _
    rw [det C P hP _ ((Λ C' _ hP').x k) hy _ (hJi C' _) _ hq hred]
    exact nsmul_val_congr L' hbase
  ·
    intro C _ _ P hP P₀ hP₀ x hx hlift
    refine (𝒰 C P hP).hom_ext _ _ fun i => ?_
    rw [hÑ]
    have hP₀' : P₀ = red₀ hπ fZ fZ₀ g hg C P hP :=
      hom_ext_Z₀ hπ fZ fZ₀ g hg _ _ (by rw [hP₀, red₀_fst])
    have hred : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ x =
        Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫ x₀ hπ fZ fZ₀ g hg ψ C P hP := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp]
      show _ = red₀ hπ fZ fZ₀ g hg C P hP ≫ ψ
      rw [← hP₀']
      exact hlift
    have hy : x ≫ f' = 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap B C)) := by
      rw [Category.id_comp]; exact hx
    have hq : Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) ≫ 𝟙 (Spec (CommRingCat.of C)) =
        Spec.map (CommRingCat.ofHom (RingHom.id _)) ≫
          Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (JJ B B₀ C))) := by
      rw [CommRingCat.ofHom_id, Spec.map_id, Category.id_comp, Category.comp_id]
    have hwu : 𝟙 _ ≫ Spec.map (CommRingCat.ofHom (algebraMap C (Localization.Away ((Λ C P hP).a i)))) =
        (𝒰 C P hP).f i ≫ 𝟙 _ := by
      rw [Category.id_comp, Category.comp_id]; rfl
    have key₁ := engine L' hc F θ hθ N hN μ _ (JJ B B₀ C) (x₀ hπ fZ fZ₀ g hg ψ C P hP) ((Λ C P hP).a i)
      ((Λ C P hP).x i) ((Λ C P hP).hx i) ((Λ C P hP).hred i) (𝟙 _) x hy (JJ B B₀ C) (JJ_pow μ hμ C)
      (RingHom.id _) hq hred (𝟙 _) ((𝒰 C P hP).f i) hwu
    rw [Category.id_comp] at key₁
    refine key₁.trans ?_
    rw [comp_nsmul_val, comp_nsmul_val]
    exact nsmul_val_congr L' (by rw [Category.id_comp]; rfl)

end S_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates
end P2MW
export P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_natural_forall_eq_nsmul_pow_of_isFormalCoordinates (solution)
