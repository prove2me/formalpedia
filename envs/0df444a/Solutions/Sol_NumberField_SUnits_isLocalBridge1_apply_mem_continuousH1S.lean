-- Prove2me | solution 1 for NumberField.SUnits.isLocalBridge1_apply_mem_continuousH1S
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/69689154-0956-5ab5-8052-1b0faa0e4f2d

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalBridge
import Theorems.Thm_IntermediateField_isUnramifiedOutside_sup_adjoin_of_pow_eq
import Theorems.Thm_NumberField_SUnits_algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_isLocalBridge1_apply_mem_continuousH1S
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

namespace LB1EX

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

def homAdd {V W : Rep.{0} k D} (χ : V ⟶ W) : V →+ W := χ.hom.toLinearMap.toAddMonoidHom

lemma homAdd_apply {V W : Rep.{0} k D} (χ : V ⟶ W) (v : V) : homAdd χ v = χ.hom v := rfl

def homOfLinear {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) : V ⟶ W :=
  Rep.ofHom ⟨L, fun d => LinearMap.ext (hL d)⟩

lemma homOfLinear_hom_apply {V W : Rep.{0} k D} (L : V →ₗ[k] W) (hL : ∀ (d : D) (v : V), L (V.ρ d v) = W.ρ d (L v)) (v : V) :
    (homOfLinear L hL).hom v = L v := rfl

def ev (ψ : (ihom (Rep.res π P)).obj A) : P →+ A := LinearMap.toAddMonoidHom (show P →ₗ[k] A from ψ)

lemma ev_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ + ψ') x = ev π ψ x + ev π ψ' x := rfl
lemma ev_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ - ψ') x = ev π ψ x - ev π ψ' x := rfl

noncomputable def cob (ψ : (ihom (Rep.res π P)).obj A) (h : H) : P →+ A := ev π ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h)

lemma cob_apply (ψ : (ihom (Rep.res π P)).obj A) (h : H) (x : P) :
    cob π ψ h x = A.ρ h (ev π ψ (P.ρ (π h⁻¹) x)) - ev π ψ x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ h ψ - ψ) x = _
  rw [ev_sub]
  congr 1

lemma cob_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ + ψ') h x = cob π ψ h x + cob π ψ' h x := by
  simp only [cob, map_add, Pi.add_apply, ev_add]

lemma cob_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : cob π (ψ - ψ') h x = cob π ψ h x - cob π ψ' h x := by
  simp only [cob, map_sub, Pi.sub_apply, ev_sub]

lemma ρ_ρ_inv {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d (V.ρ d⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

lemma ρ_one_apply {V : Rep.{0} k D} (v : V) : V.ρ 1 v = v := by
  rw [map_one, Module.End.one_apply]

lemma ρ_inv_ρ {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d⁻¹ (V.ρ d v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

section hyps

variable (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

include hκ in

lemma κ_inj {m m' : M} (h : ∀ b, κ b m = κ b m') : m = m' :=
  (hκ (κ.flip m')).unique h (fun _ => rfl)

include hfg hg hκ in

lemma exists_forall_κ_eq (c : P →+ A) (hc : ∀ x : R, c (f.hom x) = 0) : ∃ m : M, ∀ x : P, κ (g.hom x) m = c x := by
  classical

  have hker : ∀ y y' : P, g.hom y = g.hom y' → c y = c y' := by
    intro y y' hyy'
    have h0 : g.hom (y - y') = 0 := by rw [map_sub, hyy', sub_self]
    obtain ⟨x, hx⟩ := (hfg _).1 h0
    have := hc x
    rw [hx, map_sub, sub_eq_zero] at this
    exact this
  let s : B → P := Function.surjInv hg
  have hs : ∀ b, g.hom (s b) = b := Function.surjInv_eq hg
  let cB : B →+ A :=
    { toFun := fun b => c (s b)
      map_zero' := by rw [hker (s 0) 0 (by rw [hs, map_zero]), map_zero]
      map_add' := fun b b' => by rw [← map_add, hker (s (b + b')) (s b + s b') (by rw [hs, map_add, hs, hs])] }
  obtain ⟨m, hm, -⟩ := hκ cB
  exact ⟨m, fun x => by rw [hm]; exact hker _ _ (hs _)⟩

include hιeq in

lemma cob_apply_f (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A)
    (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : R) : cob π ψ h (f.hom x) = 0 := by
  rw [cob_apply, ← Rep.hom_comm_apply f, hψ, hψ, Rep.hom_comm_apply φ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

lemma κ_ρ (h : H) (b : B) (m : M) : κ b (M.ρ h m) = A.ρ h (κ (B.ρ (π h⁻¹) b) m) := by
  rw [← hκeq, map_inv, ρ_ρ_inv]

noncomputable def nOf (ψ : (ihom (Rep.res π P)).obj A) (h : H) : M := by
  classical
  exact if hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x then hex.choose else 0

include hfg hg hκ hιeq in
lemma κ_nOf (φ : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : R, ev π ψ (f.hom x) = ι (φ.hom x)) (h : H) (x : P) :
    κ (g.hom x) (nOf π g κ ψ h) = cob π ψ h x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob π ψ h x :=
    exists_forall_κ_eq f g κ hfg hg hκ (cob π ψ h) (cob_apply_f π f ι hιeq φ ψ hψ h)
  simp only [nOf, dif_pos hex]
  exact hex.choose_spec x

include hg hκ hκeq in

lemma mem_cocycles₁_of_forall_κ (ψ : (ihom (Rep.res π P)).obj A) (n : H → M)
    (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) : n ∈ cocycles₁ M := by
  rw [mem_cocycles₁_iff]
  intro h₁ h₂
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [map_add, hn, κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hn, hn]
  simp only [cob_apply, map_mul, mul_inv_rev, Module.End.mul_apply, map_sub]
  abel

include hg hκ hκeq in

lemma sub_mem_coboundaries₁ (ψ ψ' : (ihom (Rep.res π P)).obj A) (n n' : H → M)
    (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) (hn' : ∀ (h : H) (x : P), κ (g.hom x) (n' h) = cob π ψ' h x)
    (m₀ : M) (hm₀ : ∀ x : P, κ (g.hom x) m₀ = ev π (ψ - ψ') x) : n - n' ∈ coboundaries₁ M := by
  refine ⟨m₀, funext fun h => ?_⟩
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [d₀₁_hom_apply, Pi.sub_apply, map_sub, map_sub, hn, hn', κ_ρ π κ hκeq, ← Rep.hom_comm_apply g, hm₀, hm₀, ← cob_sub,
    cob_apply]

include hιeq in

lemma cob_eq_zero_of_hom (χ : P ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ x : P, ev π ψ x = ι (χ.hom x)) (h : H) (x : P) :
    cob π ψ h x = 0 := by
  rw [cob_apply, hψ, hψ, Rep.hom_comm_apply χ, ← hιeq, map_inv, ρ_ρ_inv, sub_self]

include hκeq in

lemma cob_of_κ (m₀ : M) (θ : (ihom (Rep.res π P)).obj A) (hθ : ∀ x : P, ev π θ x = κ (g.hom x) m₀) (h : H) (x : P) :
    cob π θ h x = κ (g.hom x) (M.ρ h m₀) - κ (g.hom x) m₀ := by
  rw [cob_apply, hθ, hθ, Rep.hom_comm_apply g, ← κ_ρ π κ hκeq]

lemma ρ_ev_of_cob_eq_zero (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (h : H) (x : P) :
    A.ρ h (ev π ψ x) = ev π ψ (P.ρ (π h) x) := by
  have := hψ h (P.ρ (π h) x)
  rw [cob_apply, sub_eq_zero, map_inv, ρ_inv_ρ] at this
  exact this

lemma ρ_ev_of_cob_eq_zero_of_ker (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ (h : H) (x : P), cob π ψ h x = 0) (s : H)
    (hs : π s = 1) (x : P) : A.ρ s (ev π ψ x) = ev π ψ x := by
  rw [ρ_ev_of_cob_eq_zero π ψ hψ, hs, map_one, Module.End.one_apply]

lemma ev_ext {s t : (ihom (Rep.res π P)).obj A} (hst : ∀ x : P, ev π s x = ev π t x) : s = t := LinearMap.ext hst

lemma ev_ρ (h : H) (t : (ihom (Rep.res π P)).obj A) (x : P) :
    ev π (((ihom (Rep.res π P)).obj A).ρ h t) x = A.ρ h (ev π t (P.ρ (π h⁻¹) x)) := rfl

include hg hκ in

lemma isLevelConstant₁_of_forall_κ (r : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hπlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s : H, r s ∈ F.fixingSubgroup → π s = 1)
    (ψ : (ihom (Rep.res π P)).obj A)
    (hψlev : ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
      ∀ s : H, r s ∈ F.fixingSubgroup → ∀ x : P, A.ρ s (ev π ψ x) = ev π ψ x)
    (n : H → M) (hn : ∀ (h : H) (x : P), κ (g.hom x) (n h) = cob π ψ h x) : IsLevelConstant₁ r n := by
  obtain ⟨F₁, hF₁, h₁⟩ := hπlev
  obtain ⟨F₂, hF₂, h₂⟩ := hψlev
  haveI := hF₁
  haveI := hF₂
  refine ⟨F₁ ⊔ F₂, inferInstance, fun h s hs => ?_⟩
  have hs₁ : π s = 1 := h₁ s (IntermediateField.fixingSubgroup_antitone le_sup_left hs)
  have hs₂ := h₂ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)
  apply κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hn, hn, cob_apply, cob_apply, mul_inv_rev, map_mul π, map_inv π s, hs₁, inv_one, one_mul, map_mul, Module.End.mul_apply,
    hs₂]

end hyps

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

theorem toIntLinearMapOfModules_apply {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) (m : V) : @DFunLike.coe _ _ _ (@LinearMap.instFunLike ℤ ℤ V W _ _ _ _ instV instW (RingHom.id ℤ))
      (toIntLinearMapOfModules instV instW u) m = u m := rfl

end LB1EX

namespace ExtECont

open NumberField

lemma exists_extension_of_divisible {Q : Type} [AddCommGroup Q] (hQ : ∀ n : ℕ, n ≠ 0 → ∀ a : Q, ∃ b : Q, n • b = a)
    {V W : Type} [AddCommGroup V] [AddCommGroup W] (f : V →+ W) (hf : Function.Injective f) (φ : V →+ Q) :
    ∃ ψ : W →+ Q, ∀ v : V, ψ (f v) = φ v := by
  letI : DivisibleBy Q ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn a => hQ n hn a
  letI : DivisibleBy Q ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  haveI : Module.Injective ℤ Q := (Module.Baer.of_divisible _).injective
  obtain ⟨ψ, hψ⟩ := Module.Injective.out (Q := Q) f.toIntLinearMap hf φ.toIntLinearMap
  exact ⟨ψ.toAddMonoidHom, hψ⟩

lemma units_algClosure_divisible (n : ℕ) (hn : n ≠ 0) (a : Additive (AlgebraicClosure ℚ)ˣ) :
    ∃ b : Additive (AlgebraicClosure ℚ)ˣ, n • b = a := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul a : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) (Nat.pos_of_ne_zero hn)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hz
    exact (Additive.toMul a).ne_zero hz.symm
  refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  change ((Units.mk0 z hz0 ^ n : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = _
  rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz]

lemma restrictNormalHom_eq_one_of_mem_fixingSubgroup (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [Normal ℚ ↥F]
    (s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hs : s ∈ F.fixingSubgroup) : AlgEquiv.restrictNormalHom ↥F s = 1 := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hs
  apply AlgEquiv.ext
  intro y
  apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
  change algebraMap ↥F (AlgebraicClosure ℚ) (s.restrictNormal ↥F y) = _
  rw [AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply]
  exact hs y y.2

lemma ιE_equivariant (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [Normal ℚ ↥F]
    (Sℚ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)))
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (h : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    ιE ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F h) x) =
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ h (ιE x) := by
  apply Additive.toMul.injective
  apply Units.ext
  rw [hιE, NumberField.SUnits.val_rho]
  simp only [Rep.ofAlgebraAutOnUnits, Units.coe_map, MonoidHom.coe_coe]
  change _ = ((Additive.toMul (Additive.ofMul (h • Additive.toMul (ιE x))) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
  rw [toMul_ofMul, hιE]
  exact AlgEquiv.restrictNormal_commutes h ↥F _

variable {k : Type} [CommRing k] {H : Type} [Group H] in
lemma ρ_zero {V : Rep.{0} k H} (h : H) : V.ρ h 0 = 0 := map_zero _

variable {k : Type} [CommRing k] {H : Type} [Group H] in
lemma ρ_add {V : Rep.{0} k H} (h : H) (v w : V) : V.ρ h (v + w) = V.ρ h v + V.ρ h w := map_add _ _ _

variable {k : Type} [CommRing k] {H : Type} [Group H] in
lemma ρ_neg {V : Rep.{0} k H} (h : H) (v : V) : V.ρ h (-v) = -V.ρ h v := map_neg _ _

end ExtECont

open LB1EX ExtECont in
theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    [Module.Finite ℤ P] (hB : ∀ b : B, p • b = 0)
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    {Λ : (R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ H1 M}
    (hΛ : IsLocalBridge₁ (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ Λ)
    (φ : R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) :
    Λ φ ∈ continuousH1S S M := by
  classical
  haveI : Normal ℚ ↥F := inferInstance
  let K := AlgebraicClosure ℚ
  let π : (K ≃ₐ[ℚ] K) →* (↥F ≃ₐ[ℚ] ↥F) := AlgEquiv.restrictNormalHom ↥F
  let A : Rep ℤ (K ≃ₐ[ℚ] K) := Rep.ofAlgebraAutOnUnits ℚ K
  let X := NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ

  have qψ := exists_extension_of_divisible units_algClosure_divisible (homAdd f) hf (ιE.comp (homAdd φ))
  rcases qψ with ⟨ψ, hψ⟩
  let Ψ : (ihom (Rep.res π P)).obj A := toIntLinearMapOfModules _ _ ψ
  have hΨ : ∀ x : R, ev π Ψ (f.hom x) = ιE (φ.hom x) := fun x => hψ x

  have hιeq : ∀ (h : K ≃ₐ[ℚ] K) (x : X), ιE (X.ρ (π h) x) = A.ρ h (ιE x) := fun h x => ιE_equivariant F Sℚ ιE hιE h x
  have hκeq' : ∀ (h : K ≃ₐ[ℚ] K) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m) := fun h b m => hκeq h b m
  let n : (K ≃ₐ[ℚ] K) → M := nOf π g κ Ψ
  have hn : ∀ (h : K ≃ₐ[ℚ] K) (x : P), κ (g.hom x) (n h) = cob π Ψ h x := κ_nOf π f g ιE κ hfg hg hιeq hκ φ Ψ hΨ
  have hcoc : n ∈ cocycles₁ M := mem_cocycles₁_of_forall_κ π g κ hg hκeq' hκ Ψ n hn
  have hΛφ : Λ φ = (H1π M).hom ⟨n, hcoc⟩ := hΛ φ Ψ hΨ n hn hcoc

  have hlev : IsLevelConstantS₁ S n := by

    obtain ⟨s₀, hs₀⟩ := Module.Finite.fg_top (R := ℤ) (M := P)
    have hpx : ∀ x : P, ∃ r : R, f.hom r = p • x := fun x => (hfg (p • x)).1 (by
      change homAdd g (p • x) = 0
      rw [map_nsmul, homAdd_apply]
      exact hB _)
    choose rOf hrOf using hpx
    let u : P → (↥F)ˣ := fun x => NumberField.SUnits.val ℚ ↥F Sℚ (φ.hom (rOf x))
    let α : P → K := fun x => ((Additive.toMul (ψ x) : Kˣ) : K)
    have hα : ∀ x, α x ^ p = algebraMap ↥F K (u x : ↥F) := by
      intro x
      have h1 : ψ (p • x) = ιE (φ.hom (rOf x)) := by rw [← hrOf]; exact hψ (rOf x)
      have h2 := congrArg (fun a => ((Additive.toMul a : Kˣ) : K)) h1
      simp only [map_nsmul, toMul_nsmul, Units.val_pow_eq_pow_val, hιE, Units.coe_map, MonoidHom.coe_coe] at h2
      exact h2
    have hxS : ∀ x, ∀ q : Nat.Primes, q ∉ S → ∀ Av : ValuationSubring K, Av.LiesOverPrime (q : ℕ) →
        algebraMap ↥F K (u x : ↥F) ∈ Av ∧ (algebraMap ↥F K (u x : ↥F))⁻¹ ∈ Av := fun x q hq Av hAv =>
      NumberField.SUnits.algebraMap_mem_and_inv_mem_of_mem_sUnits_of_liesOverPrime S Sℚ hSℚ F (u x)
        (NumberField.SUnits.val_mem ℚ ↥F Sℚ _) q hq Av hAv

    have hF₂ : ∀ t : Finset P, (F ⊔ IntermediateField.adjoin ℚ (α '' (↑t : Set P))).IsUnramifiedOutside S := by
      intro t
      induction t using Finset.induction_on with
      | empty =>
        rw [Finset.coe_empty, Set.image_empty, IntermediateField.adjoin_empty, sup_bot_eq]
        exact hF
      | insert x t hxt ih =>
        rw [Finset.coe_insert, Set.image_insert_eq, Set.insert_eq, IntermediateField.adjoin_union,
          sup_comm (IntermediateField.adjoin ℚ {α x}), ← sup_assoc]
        exact IntermediateField.isUnramifiedOutside_sup_adjoin_of_pow_eq S (pPrime p) hpS _ ih (algebraMap ↥F K (u x : ↥F))
          ((le_sup_left : F ≤ F ⊔ IntermediateField.adjoin ℚ (α '' ↑t)) (u x : ↥F).2) (hxS x) (α x) (hα x)
    refine ⟨F ⊔ IntermediateField.adjoin ℚ (α '' (↑s₀ : Set P)), hF₂ s₀, fun h s hs => ?_⟩
    have hsF : s ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone le_sup_left hs
    have hπs : π s = 1 := restrictNormalHom_eq_one_of_mem_fixingSubgroup F s hsF

    have hfixgen : ∀ x ∈ s₀, A.ρ s (ψ x) = ψ x := by
      intro x hx
      have hsα : s (α x) = α x := by
        rw [IntermediateField.mem_fixingSubgroup_iff] at hs
        exact hs _ ((le_sup_right : _ ≤ F ⊔ IntermediateField.adjoin ℚ (α '' ↑s₀)) (IntermediateField.subset_adjoin ℚ _ ⟨x, hx, rfl⟩))
      apply Additive.toMul.injective
      apply Units.ext
      exact hsα
    have hfix : ∀ x : P, A.ρ s (ψ x) = ψ x := by
      intro x
      have hxmem : x ∈ (Submodule.span ℤ (↑s₀ : Set P)).toAddSubgroup := by rw [hs₀]; trivial
      rw [Submodule.span_int_eq_addSubgroupClosure] at hxmem
      induction hxmem using AddSubgroup.closure_induction with
      | mem y hy => exact hfixgen y hy
      | zero =>
        rw [map_zero]
        exact map_zero (A.ρ s)
      | add y z _ _ hy hz =>
        rw [map_add]
        refine (map_add (A.ρ s) _ _).trans ?_
        rw [hy, hz]
        rfl
      | neg y _ hy =>
        rw [map_neg]
        refine (map_neg (A.ρ s) _).trans ?_
        rw [hy]
        rfl

    apply κ_inj (B := B) (A := A) κ hκ
    intro b
    obtain ⟨x, rfl⟩ := hg b
    refine (hn (h * s) x).trans (Eq.trans ?_ (hn h x).symm)
    rw [cob_apply, cob_apply, mul_inv_rev, map_mul π, map_inv π s, hπs, inv_one, one_mul, map_mul, Module.End.mul_apply]
    congr 1
    exact congrArg _ (hfix _)

  rw [hΛφ]
  exact (mem_continuousH1S_iff S M _).2 ⟨⟨n, hcoc⟩, hlev, rfl⟩

end S_NumberField_SUnits_isLocalBridge1_apply_mem_continuousH1S
end P2MW
export P2MW.S_NumberField_SUnits_isLocalBridge1_apply_mem_continuousH1S (solution)
