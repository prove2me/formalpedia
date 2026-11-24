-- Prove2me | solution 1 for GlobalTheory.EvHopf.evHopf_of_tensorLocal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T14:27:44.345913+00:00
-- url     : https://prove2.me/submissions/f8782d69-f793-46ed-afde-5eff38c71189

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_EvHopfStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_EvHopfOfTensorLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
set_option linter.style.haveILetI false
namespace GlobalTheory.EvHopf
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem ptMap_comp_sO_and_map_y (t : _root_.ReciprocityTheory.PGsh.Up.Nb p g) :
    (D.ptMap t).comp (D.fin.sO (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O ∧
      B.map (D.ptMap t) (D.fin.y (D.ptIdx t)) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := by
  have h := Classical.choose_spec
    (Classical.choose_spec (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ (D.pt_p t)))
  exact ⟨h.1, h.2.1⟩
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem evAll_apply (C : Type) [Field C] [Algebra Tw.O.carrier C]
    (a : (i : D.fin.ι) → (D.fin.AAx i).carrier) (t : _root_.ReciprocityTheory.PGsh.Up.Nb p g) :
    D.evAll C a t = algebraMap Tw.O.carrier C ((D.ptMap t).1 (a (D.ptIdx t))) := rfl
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem retraction_apply_eq_ptMap (t : _root_.ReciprocityTheory.PGsh.Up.Nb p g) (i : D.fin.ι)
    (φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O) (h₁ : φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O)
    (h₂ : B.map φ (D.fin.y i) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t) (a : (j : D.fin.ι) → (D.fin.AAx j).carrier) :
    φ.1 (a i) = (D.ptMap t).1 (a (D.ptIdx t)) := by
  have h := Classical.choose_spec
    (Classical.choose_spec (D.fin.univ Tw.O (_root_.ReciprocityTheory.PGsh.LHom.id _) _ (D.pt_p t)))
  obtain ⟨rfl, hh⟩ := h.2.2 i φ h₁ h₂
  rw [eq_of_heq hh]
  rfl
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem tensor_evAll_mem_tensorSpan (C : Type) [Field C] [Algebra Tw.O.carrier C] (j k : D.fin.ι) :
    letI := _root_.ReciprocityTheory.PGsh.Be2.algOf (D.fin.sO j); letI := _root_.ReciprocityTheory.PGsh.Be2.algOf (D.fin.sO k)
    ∀ x : (D.fin.AAx j).carrier ⊗[Tw.O.carrier] (D.fin.AAx k).carrier,
    ∃ G ∈ _root_.ReciprocityTheory.PGsh.L2.tensorSpan Tw.O.carrier (D.evImg C),
      (∀ t t', ¬ (D.ptIdx t = j ∧ D.ptIdx t' = k) → G (t, t') = 0) ∧
      ∀ (t t' : _root_.ReciprocityTheory.PGsh.Up.Nb p g) (φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O) (hφ : φ.comp (D.fin.sO j) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O)
        (φ' : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx k) Tw.O) (hφ' : φ'.comp (D.fin.sO k) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O),
        B.map φ (D.fin.y j) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t → B.map φ' (D.fin.y k) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t' →
        G (t, t') = algebraMap Tw.O.carrier C
          (Algebra.TensorProduct.lift (_root_.GlobalTheory.EvHopf.secAlg _ φ hφ)
            (_root_.GlobalTheory.EvHopf.secAlg _ φ' hφ') (fun _ _ => Commute.all _ _) x) := by
  intro x
  letI := _root_.ReciprocityTheory.PGsh.Be2.algOf (D.fin.sO j)
  letI := _root_.ReciprocityTheory.PGsh.Be2.algOf (D.fin.sO k)
  classical
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, zero_mem _, fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => by simp⟩
  | tmul b c =>
    refine ⟨fun q => D.evAll C (Pi.single (M := fun i => (D.fin.AAx i).carrier) j b) q.1 *
      D.evAll C (Pi.single (M := fun i => (D.fin.AAx i).carrier) k c) q.2, ?_, ?_, ?_⟩
    · unfold _root_.ReciprocityTheory.PGsh.L2.tensorSpan _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg
      exact Submodule.subset_span ⟨_, Submodule.subset_span ⟨_, rfl⟩, _,
        Submodule.subset_span ⟨_, rfl⟩, rfl⟩
    · intro t t' h
      simp only [evAll_apply]
      by_cases hj : D.ptIdx t = j
      · have hk : D.ptIdx t' ≠ k := fun hk => h ⟨hj, hk⟩
        rw [Pi.single_eq_of_ne hk, map_zero, map_zero, mul_zero]
      · rw [Pi.single_eq_of_ne hj, map_zero, map_zero, zero_mul]
    · intro t t' φ hφ φ' hφ' h₁ h₂
      simp only [evAll_apply]
      rw [← retraction_apply_eq_ptMap D t j φ hφ h₁ (Pi.single j b),
        ← retraction_apply_eq_ptMap D t' k φ' hφ' h₂ (Pi.single k c),
        Pi.single_eq_same, Pi.single_eq_same, Algebra.TensorProduct.lift_tmul, map_mul]
      rfl
  | add x y hx hy =>
    obtain ⟨G, hG, h0, h1⟩ := hx
    obtain ⟨G', hG', h0', h1'⟩ := hy
    refine ⟨G + G', add_mem hG hG', fun t t' h => by simp [h0 t t' h, h0' t t' h],
      fun t t' φ hφ φ' hφ' e e' => ?_⟩
    simp only [Pi.add_apply, h1 t t' φ hφ φ' hφ' e e', h1' t t' φ hφ φ' hφ' e e', map_add]
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem lHom_comp_assoc {R S T U : _root_.ReciprocityTheory.PGsh.LAlg R₀} (f : _root_.ReciprocityTheory.PGsh.LHom T U) (f' : _root_.ReciprocityTheory.PGsh.LHom S T)
    (f'' : _root_.ReciprocityTheory.PGsh.LHom R S) : (f.comp f').comp f'' = f.comp (f'.comp f'') := rfl
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem p_nsmul_tau_zero (j : _root_.ReciprocityTheory.PGsh.Up.Ix g) : p • D.L.τ j 0 = 0 := by
  classical
  have h := D.pt_p (Pi.single j 1 : _root_.ReciprocityTheory.PGsh.Up.Ix g → ZMod p)
  unfold _root_.ReciprocityTheory.PGsh.Be2.ptOf at h
  rwa [Finset.sum_eq_single j (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp),
    Pi.single_eq_same, ZMod.val_one, one_smul] at h
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem ptOf_add_unramified_depth (t t' : _root_.ReciprocityTheory.PGsh.Up.Nb p g) :
    _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (t + t') = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t + _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t' := by
  unfold _root_.ReciprocityTheory.PGsh.Be2.ptOf
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hp := p_nsmul_tau_zero D j
  have key : ∀ n : ℕ, n • D.L.τ j 0 = (n % p) • D.L.τ j 0 := fun n => by
    conv_lhs => rw [← Nat.mod_add_div n p]
    rw [add_nsmul, mul_nsmul, hp, nsmul_zero, add_zero]
  rw [← add_nsmul, key ((t j).val + (t' j).val), ← ZMod.val_add]
  rfl
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem exists_tensorSpan_eq_evAll_add (hTL : _root_.GlobalTheory.EvHopf.TensorLocal) (C : Type) [Field C]
    [Algebra Tw.O.carrier C] (a : (i : D.fin.ι) → (D.fin.AAx i).carrier) (j k : D.fin.ι) :
    ∃ G ∈ _root_.ReciprocityTheory.PGsh.L2.tensorSpan Tw.O.carrier (D.evImg C),
      (∀ t t', ¬ (D.ptIdx t = j ∧ D.ptIdx t' = k) → G (t, t') = 0) ∧
      ∀ t t', D.ptIdx t = j → D.ptIdx t' = k → G (t, t') = D.evAll C a (t + t') := by
  classical
  by_cases hex : ∃ t₀ t₀' : _root_.ReciprocityTheory.PGsh.Up.Nb p g, D.ptIdx t₀ = j ∧ D.ptIdx t₀' = k
  swap
  · exact ⟨0, zero_mem _, fun _ _ _ => rfl, fun t t' ht ht' => (hex ⟨t, t', ht, ht'⟩).elim⟩
  obtain ⟨t₀, t₀', h₀, h₀'⟩ := hex
  have hcl : ∀ (t : _root_.ReciprocityTheory.PGsh.Up.Nb p g) (i : D.fin.ι), D.ptIdx t = i →
      ∃ φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx i) Tw.O,
        φ.comp (D.fin.sO i) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O ∧ B.map φ (D.fin.y i) = _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := by
    rintro t i rfl
    exact ⟨_, ptMap_comp_sO_and_map_y D t⟩
  obtain ⟨φ₀, hφ₀, -⟩ := hcl t₀ j h₀
  obtain ⟨φ₀', hφ₀', -⟩ := hcl t₀' k h₀'
  letI := _root_.ReciprocityTheory.PGsh.Be2.algOf (D.fin.sO j)
  letI := _root_.ReciprocityTheory.PGsh.Be2.algOf (D.fin.sO k)
  haveI : Module.Finite Tw.O.carrier (D.fin.AAx j).carrier := (D.fin.free j).2
  haveI : Module.Finite Tw.O.carrier (D.fin.AAx k).carrier := (D.fin.free k).2
  haveI hloc : IsLocalRing ((D.fin.AAx j).carrier ⊗[Tw.O.carrier] (D.fin.AAx k).carrier) :=
    hTL _ _ _ (_root_.GlobalTheory.EvHopf.secAlg _ φ₀ hφ₀) (_root_.GlobalTheory.EvHopf.secAlg _ φ₀' hφ₀')
  letI : Algebra R₀ ((D.fin.AAx j).carrier ⊗[Tw.O.carrier] (D.fin.AAx k).carrier) :=
    RingHom.toAlgebra (Algebra.TensorProduct.includeLeftRingHom.comp
      (algebraMap R₀ (D.fin.AAx j).carrier))
  let S : _root_.ReciprocityTheory.PGsh.LAlg R₀ := ⟨(D.fin.AAx j).carrier ⊗[Tw.O.carrier] (D.fin.AAx k).carrier⟩
  let ev := fun (φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O) (hφ : φ.comp (D.fin.sO j) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O)
      (φ' : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx k) Tw.O) (hφ' : φ'.comp (D.fin.sO k) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O) =>
    Algebra.TensorProduct.lift (_root_.GlobalTheory.EvHopf.secAlg _ φ hφ) (_root_.GlobalTheory.EvHopf.secAlg _ φ' hφ')
      (fun _ _ => Commute.all _ _)
  have ev_tmul : ∀ φ hφ φ' hφ' (b : (D.fin.AAx j).carrier) (c : (D.fin.AAx k).carrier),
      ev φ hφ φ' hφ' (b ⊗ₜ c) = φ.1 b * φ'.1 c := fun _ _ _ _ _ _ =>
    Algebra.TensorProduct.lift_tmul _ _ _ _ _
  let Φ : ∀ (φ : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) Tw.O) (hφ : φ.comp (D.fin.sO j) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O)
      (φ' : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx k) Tw.O) (hφ' : φ'.comp (D.fin.sO k) = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O),
      _root_.ReciprocityTheory.PGsh.LHom S Tw.O := fun φ hφ φ' hφ' =>
    ⟨{ toRingHom := (ev φ hφ φ' hφ').toRingHom
       commutes' := fun r => by
         show ev φ hφ φ' hφ' (algebraMap R₀ (D.fin.AAx j).carrier r ⊗ₜ 1) = _
         rw [ev_tmul, map_one, mul_one]
         exact φ.1.commutes r },
      IsLocalHom.of_surjective _ (fun o => ⟨algebraMap Tw.O.carrier _ o,
        (ev φ hφ φ' hφ').commutes o⟩)⟩
  let sT : _root_.ReciprocityTheory.PGsh.LHom Tw.O S :=
    ⟨{ toRingHom := algebraMap Tw.O.carrier ((D.fin.AAx j).carrier ⊗[Tw.O.carrier] (D.fin.AAx k).carrier)
       commutes' := fun r => by
         show algebraMap Tw.O.carrier (D.fin.AAx j).carrier (algebraMap R₀ Tw.O.carrier r) ⊗ₜ 1 =
           algebraMap R₀ (D.fin.AAx j).carrier r ⊗ₜ 1
         congr 1
         exact (D.fin.sO j).1.commutes r },
      ⟨fun o hu => by
        exact (congrArg IsUnit ((ev φ₀ hφ₀ φ₀' hφ₀').commutes o)).mp (hu.map (ev φ₀ hφ₀ φ₀' hφ₀'))⟩⟩
  let inclL : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx j) S :=
    ⟨{ toRingHom := Algebra.TensorProduct.includeLeftRingHom
       commutes' := fun r => rfl },
      ⟨fun b hu => by
        have := hu.map (ev φ₀ hφ₀ φ₀' hφ₀')
        have h3 : ev φ₀ hφ₀ φ₀' hφ₀' (Algebra.TensorProduct.includeLeftRingHom b) = φ₀.1 b := by
          show ev φ₀ hφ₀ φ₀' hφ₀' (b ⊗ₜ 1) = _
          rw [ev_tmul, map_one, mul_one]
        have h2 : IsUnit (φ₀.1 b) := h3 ▸ this
        exact φ₀.2.map_nonunit b h2⟩⟩
  let inclR : _root_.ReciprocityTheory.PGsh.LHom (D.fin.AAx k) S :=
    ⟨{ toRingHom := Algebra.TensorProduct.includeRight.toRingHom
       commutes' := fun r => by
         show (1 : (D.fin.AAx j).carrier) ⊗ₜ algebraMap R₀ (D.fin.AAx k).carrier r =
           algebraMap R₀ (D.fin.AAx j).carrier r ⊗ₜ 1
         have e₁ : algebraMap R₀ (D.fin.AAx k).carrier r =
             algebraMap Tw.O.carrier (D.fin.AAx k).carrier (algebraMap R₀ Tw.O.carrier r) :=
           ((D.fin.sO k).1.commutes r).symm
         have e₂ : algebraMap R₀ (D.fin.AAx j).carrier r =
             algebraMap Tw.O.carrier (D.fin.AAx j).carrier (algebraMap R₀ Tw.O.carrier r) :=
           ((D.fin.sO j).1.commutes r).symm
         rw [e₁, e₂, Algebra.algebraMap_eq_smul_one (A := (D.fin.AAx k).carrier),
           Algebra.algebraMap_eq_smul_one (A := (D.fin.AAx j).carrier), TensorProduct.tmul_smul,
           TensorProduct.smul_tmul'] },
      ⟨fun c hu => by
        have := hu.map (ev φ₀ hφ₀ φ₀' hφ₀')
        have h3 : ev φ₀ hφ₀ φ₀' hφ₀' (Algebra.TensorProduct.includeRight c) = φ₀'.1 c := by
          show ev φ₀ hφ₀ φ₀' hφ₀' (1 ⊗ₜ c) = _
          rw [ev_tmul, map_one, one_mul]
        have h2 : IsUnit (φ₀'.1 c) := h3 ▸ this
        exact φ₀'.2.map_nonunit c h2⟩⟩
  have hΦs : ∀ φ hφ φ' hφ', (Φ φ hφ φ' hφ').comp sT = _root_.ReciprocityTheory.PGsh.LHom.id Tw.O := fun φ hφ φ' hφ' =>
    Subtype.ext (AlgHom.ext fun o => (ev φ hφ φ' hφ').commutes o)
  have hΦL : ∀ φ hφ φ' hφ', (Φ φ hφ φ' hφ').comp inclL = φ := fun φ hφ φ' hφ' =>
    Subtype.ext (AlgHom.ext fun b => by
      show ev φ hφ φ' hφ' (b ⊗ₜ 1) = φ.1 b
      rw [ev_tmul, map_one, mul_one])
  have hΦR : ∀ φ hφ φ' hφ', (Φ φ hφ φ' hφ').comp inclR = φ' := fun φ hφ φ' hφ' =>
    Subtype.ext (AlgHom.ext fun c => by
      show ev φ hφ φ' hφ' (1 ⊗ₜ c) = φ'.1 c
      rw [ev_tmul, map_one, one_mul])
  have hz : p • (B.map inclL (D.fin.y j) + B.map inclR (D.fin.y k)) = 0 := by
    rw [smul_add, ← map_nsmul, ← map_nsmul, D.fin.y_p, D.fin.y_p, map_zero, map_zero, add_zero]
  obtain ⟨i, ψ, hψ₁, hψ₂, -⟩ := D.fin.univ S sT _ hz
  obtain ⟨G, hG, h0, h1⟩ := tensor_evAll_mem_tensorSpan D C j k (ψ.1 (a i))
  refine ⟨G, hG, h0, fun t t' ht ht' => ?_⟩
  obtain ⟨φ, hφ, e⟩ := hcl t j ht
  obtain ⟨φ', hφ', e'⟩ := hcl t' k ht'
  rw [h1 t t' φ hφ φ' hφ' e e', evAll_apply]
  congr 1
  refine retraction_apply_eq_ptMap D (t + t') i ((Φ φ hφ φ' hφ').comp ψ) ?_ ?_ a
  · rw [lHom_comp_assoc, hψ₁, hΦs]
  · rw [_root_.ReciprocityTheory.PGsh.BX.map_comp, hψ₂, map_add, ← _root_.ReciprocityTheory.PGsh.BX.map_comp, ← _root_.ReciprocityTheory.PGsh.BX.map_comp, hΦL, hΦR, e, e',
      ptOf_add_unramified_depth]
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem ptOf_neg' (t : _root_.ReciprocityTheory.PGsh.Up.Nb p g) :
    _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (-t) = - _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ t := by
  have h := ptOf_add_unramified_depth D (-t) t
  rw [neg_add_cancel] at h
  have h0 : _root_.ReciprocityTheory.PGsh.Be2.ptOf B D.L.τ (0 : _root_.ReciprocityTheory.PGsh.Up.Nb p g) = 0 := by
    unfold _root_.ReciprocityTheory.PGsh.Be2.ptOf; simp
  rw [h0] at h
  exact eq_neg_of_add_eq_zero_left h.symm
open TensorProduct IsLocalRing Matrix in
set_option linter.style.haveILetI false in
variable {R₀ : Type} [CommRing R₀] in
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp) in
private theorem evAll_comp_neg_mem_evImg (C : Type) [Field C] [Algebra Tw.O.carrier C]
    (a : (i : D.fin.ι) → (D.fin.AAx i).carrier) :
    (fun x => D.evAll C a (-x)) ∈ D.evImg C := by
  have hu := fun j => D.fin.univ (D.fin.AAx j) (D.fin.sO j) (-D.fin.y j)
    (by rw [smul_neg, D.fin.y_p, neg_zero])
  choose i ψ hψ using hu
  unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg
  refine Submodule.subset_span ⟨fun j => (ψ j).1 (a (i j)), ?_⟩
  funext t
  rw [evAll_apply, evAll_apply]
  congr 1
  have hP := ptMap_comp_sO_and_map_y D t
  refine (retraction_apply_eq_ptMap D (-t) (i (D.ptIdx t)) ((D.ptMap t).comp (ψ (D.ptIdx t)))
    ?_ ?_ a)
  · rw [lHom_comp_assoc, (hψ _).1, hP.1]
  · rw [_root_.ReciprocityTheory.PGsh.BX.map_comp, (hψ _).2.1, map_neg, hP.2, ptOf_neg']
end GlobalTheory.EvHopf
end
end

set_option autoImplicit false
noncomputable section
open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2
set_option linter.style.haveILetI false
open GlobalTheory GlobalTheory.EvHopf
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp)
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]
open TensorProduct IsLocalRing Matrix
set_option linter.style.haveILetI false
variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp)
variable (C : Type) [Field C] [Algebra (Tw.O : Type) C]
namespace GlobalTheory.EvHopf
namespace _root_.GlobalTheory.EvHopf
theorem _root_.solution :
  (∀ (O A A' : Type) [CommRing O] [CommRing A] [CommRing A'] [IsLocalRing O] [IsLocalRing A] [IsLocalRing A'] [Algebra O A] [Algebra O A']
    [Module.Finite O A] [Module.Finite O A'], (A →ₐ[O] O) → (A' →ₐ[O] O) → IsLocalRing (A ⊗[O] A')) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : _root_.ReciprocityTheory.PGsh.BX R₀} {Tw : _root_.ReciprocityTheory.PGsh.ATowerL R₀ p} {Dt : _root_.ReciprocityTheory.PGsh.DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : _root_.ReciprocityTheory.PGsh.Be2.Dat p g B Tw Dt Oe σ cp), _root_.ReciprocityTheory.PGsh.Be2.EvHopfStatement D) := by
  intro hTL R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  unfold _root_.ReciprocityTheory.PGsh.Be2.EvHopfStatement
  intro C _ _ _
  refine ⟨fun f hf => ?_, fun f hf => ?_⟩
  · unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg at hf
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      classical
      choose G hG h0 h1 using exists_tensorSpan_eq_evAll_add D hTL C a
      have hsum : _root_.ReciprocityTheory.PGsh.L2.addPull Tw.O.carrier (_root_.ReciprocityTheory.PGsh.Up.Nb p g) (D.evAll C a) =
          ∑ jk : D.fin.ι × D.fin.ι, G jk.1 jk.2 := by
        funext q
        obtain ⟨t, t'⟩ := q
        rw [Finset.sum_apply, Finset.sum_eq_single (D.ptIdx t, D.ptIdx t')]
        · exact (h1 _ _ t t' rfl rfl).symm
        · rintro ⟨j, k⟩ _ hne
          exact h0 j k t t' (fun h => hne (by rw [h.1, h.2]))
        · simp
      rw [hsum]
      exact Submodule.sum_mem _ fun jk _ => hG jk.1 jk.2
    | zero => rw [map_zero]; exact zero_mem _
    | add f f' _ _ hf hf' => rw [map_add]; exact add_mem hf hf'
    | smul r f _ hf => rw [map_smul]; exact Submodule.smul_mem _ r hf
  · unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg at hf ⊢
    induction hf using Submodule.span_induction with
    | mem f hf =>
      obtain ⟨a, rfl⟩ := hf
      have h := evAll_comp_neg_mem_evImg D C a
      unfold _root_.ReciprocityTheory.PGsh.Be2.Dat.evImg at h
      exact h
    | zero => exact zero_mem _
    | add f f' _ _ hf hf' => exact add_mem hf hf'
    | smul r f _ hf => exact Submodule.smul_mem _ r hf
end _root_.GlobalTheory.EvHopf
end GlobalTheory.EvHopf
