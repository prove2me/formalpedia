-- Prove2me | solution 1 for NumberField.PlaceDecomp.exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0aef9229-74c6-5704-9ff4-642c2a33ada2

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_ContinuousDuality
import Definitions.Def_GroupCohomology_CupProduct
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_Selmer
import Definitions.Def_DualSelmer_ExtConditions
import Definitions.Def_ExtCitation_KummerBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 6400000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

namespace BridgeCup

noncomputable scoped instance divisibleBy_additive_units (K : Type) [Field K] [IsAlgClosed K] :
    DivisibleBy (Additive Kˣ) ℤ :=
  divisibleByOfSMulRightSurj (Additive Kˣ) ℤ fun {n} hn a => by
    have hk : 0 < n.natAbs := Int.natAbs_pos.2 hn
    obtain ⟨v, hv⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul a : Kˣ) : K) hk
    have hv0 : v ≠ 0 := fun h0 => (Additive.toMul a).ne_zero (by rw [← hv, h0, zero_pow hk.ne'])
    have hw : (Units.mk0 v hv0) ^ n.natAbs = Additive.toMul a := Units.ext (by simp [hv])
    rcases Int.natAbs_eq n with h | h
    · refine ⟨Additive.ofMul (Units.mk0 v hv0), ?_⟩
      change Additive.ofMul ((Units.mk0 v hv0) ^ n) = a
      rw [h, zpow_natCast, hw]
      rfl
    · refine ⟨Additive.ofMul (Units.mk0 v hv0)⁻¹, ?_⟩
      change Additive.ofMul ((Units.mk0 v hv0)⁻¹ ^ n) = a
      rw [h, zpow_neg, inv_zpow, inv_inv, zpow_natCast, hw]
      rfl

theorem exists_extension {R P A : Type} [AddCommGroup R] [AddCommGroup P] [AddCommGroup A] [DivisibleBy A ℤ]
    (f : R →+ P) (hf : Function.Injective f) (φ : R →+ A) : ∃ ψ : P →+ A, ∀ r, ψ (f r) = φ r := by
  haveI : Mono (AddCommGrpCat.ofHom f) := (AddCommGrpCat.mono_iff_injective _).2 hf
  obtain ⟨h, hh⟩ := Injective.factors (AddCommGrpCat.ofHom φ) (AddCommGrpCat.ofHom f)
  refine ⟨h.hom, fun r => ?_⟩
  have := congrArg (fun k => k.hom r) hh
  simpa using this

section Core

universe u
variable {k : Type u} [CommRing k] {H D : Type u} [Group H] [Group D] (π : H →* D)
  (P : Rep.{u} k D) (A : Rep.{u} k H)

abbrev ev (ψ : (ihom (Rep.res π P)).obj A) : P →ₗ[k] A := ψ

noncomputable def cob (ψ : (ihom (Rep.res π P)).obj A) (h : H) (x : P) : A := ev π P A ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h) x

set_option backward.isDefEq.respectTransparency false in
lemma cob_apply (ψ : (ihom (Rep.res π P)).obj A) (h : H) (x : P) :
    cob π P A ψ h x = A.ρ h (ev π P A ψ (P.ρ (π h⁻¹) x)) - ev π P A ψ x := by
  unfold cob
  rw [d₀₁_hom_apply]
  rfl

lemma ρ_inv_ρ (h : H) (x : P) : P.ρ (π h⁻¹) (P.ρ (π h) x) = x := by
  rw [map_inv, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem inflate_psi_d₁₂_sub_d₁₂ (ψ : (ihom (Rep.res π P)).obj A) (nt : D → P) (g h : H) :
    ev π P A ψ (P.ρ (π g) (nt (π h)) - nt (π (g * h)) + nt (π g))
      - (d₁₂ A).hom (fun g => ev π P A ψ (nt (π g))) (g, h)
      = - cob π P A ψ g (P.ρ (π g) (nt (π h))) := by
  rw [d₁₂_hom_apply, cob_apply, ρ_inv_ρ, map_add, map_sub]
  abel

end Core

section Bridge

universe u
variable {k k' : Type u} [CommRing k] [CommRing k'] {H D : Type u} [Group H] [Group D] (π : H →* D)
  {P B : Rep.{u} k D} (g : P ⟶ B) {A : Rep.{u} k H} {M : Rep.{u} k' H} (κ' : B →+ M →+ A)
  (hκeq : ∀ (h : H) (b : B) (m : M), κ' (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ' b m))

lemma ρ_ρ_inv (h : H) (x : P) : P.ρ (π h) (P.ρ (π h⁻¹) x) = x := by
  rw [map_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

include hκeq in

lemma ρ_kappa (h : H) (x : P) (m : M) : A.ρ h (κ' (g.hom (P.ρ (π h⁻¹) x)) m) = κ' (g.hom x) (M.ρ h m) := by
  rw [← hκeq, ← Rep.hom_comm_apply g, ρ_ρ_inv]

include hκeq in

theorem cob_shift (ψ ψ' : (ihom (Rep.res π P)).obj A) (m₀ : M)
    (hψ' : ∀ x : P, ev π P A ψ' x = ev π P A ψ x + κ' (g.hom x) m₀)
    (n : H → M) (hn : ∀ (h : H) (x : P), κ' (g.hom x) (n h) = cob π P A ψ h x) (h : H) (x : P) :
    κ' (g.hom x) (n h + (d₀₁ M).hom m₀ h) = cob π P A ψ' h x := by
  rw [map_add, hn, cob_apply, cob_apply, hψ', hψ', map_add (A.ρ h), ρ_kappa π g κ' hκeq, d₀₁_hom_apply,
    map_sub (κ' (g.hom x))]
  abel

end Bridge

section Delta

universe u
variable {k : Type u} [CommRing k] {D : Type u} [Group D] {T : ShortComplex (Rep.{u} k D)} (hT : T.ShortExact)
  {X : Rep.{u} k D} (aw : T.X₁ ⟶ X)

include hT in
theorem exists_lift_repr (nD : cocycles₁ T.X₃) (x : cocycles₂ X) (y1 : groupCohomology T.X₃ 1)
    (hy1 : y1 = (H1π T.X₃).hom nD)
    (hx : (H2π X).hom x = (groupCohomology.map (MonoidHom.id D) aw 2).hom
      ((groupCohomology.δ hT 1 2 rfl).hom y1)) :
    ∃ (nt : D → T.X₂) (x₀ : D × D → T.X₁) (b₁ : D → X),
      (∀ d, T.g.hom (nt d) = nD d) ∧ (∀ dd, T.f.hom (x₀ dd) = (d₁₂ T.X₂).hom nt dd) ∧
      (∀ dd, x dd = aw.hom (x₀ dd) + (d₁₂ X).hom b₁ dd) := by
  subst hy1

  have hg : Function.Surjective T.g.hom := (Rep.epi_iff_surjective T.g).1 hT.epi_g
  choose nt hnt using fun d => hg (nD d)

  have hex := (ShortComplex.moduleCat_exact_iff _).1 (hT.exact.map (forget₂ (Rep k D) (ModuleCat k)))
  have hrange : ∀ dd, ∃ r : T.X₁, T.f.hom r = (d₁₂ T.X₂).hom nt dd := by
    rintro ⟨d₁, d₂⟩
    have h0 := congrFun (cocycles₁.d₁₂_apply nD) (d₁, d₂)
    rw [d₁₂_hom_apply] at h0
    refine hex ((d₁₂ T.X₂).hom nt (d₁, d₂)) ?_
    change T.g.hom ((d₁₂ T.X₂).hom nt (d₁, d₂)) = 0
    rw [d₁₂_hom_apply, map_add, map_sub, Rep.hom_comm_apply, hnt, hnt, hnt]
    exact h0
  choose x₀ hx₀ using hrange
  have hδ := δ₁_apply hT nD nt (funext hnt) x₀ (funext hx₀)
  change (H2π X).hom x = (groupCohomology.map (MonoidHom.id D) aw 2).hom ((groupCohomology.δ hT 1 2 rfl) (H1π T.X₃ nD)) at hx
  rw [hδ] at hx
  erw [H2π_comp_map_apply] at hx
  change H2π X x = H2π X _ at hx
  rw [H2π_eq_iff] at hx
  obtain ⟨b₁, hb₁⟩ := hx
  refine ⟨nt, x₀, b₁, hnt, hx₀, fun dd => ?_⟩
  obtain ⟨d₁, d₂⟩ := dd
  have := congrFun hb₁ (d₁, d₂)
  rw [this]
  change x (d₁, d₂) = aw.hom (x₀ (d₁, d₂)) + (x (d₁, d₂) - aw.hom (x₀ (d₁, d₂)))
  rw [add_sub_cancel]

end Delta

section Conj

universe u
variable {k : Type u} [CommRing k] {Γ : Type u} [Group Γ] {V : Rep.{u} k Γ}

theorem smul_apply_conj (c : cocycles₁ V) (σ τ : Γ) :
    V.ρ σ (c (σ⁻¹ * τ * σ)) = c τ + (V.ρ τ (c σ) - c σ) := by
  have h1 := (mem_cocycles₁_iff c).1 c.2
  have hinv : V.ρ σ (c σ⁻¹) = - c σ := by
    have := h1 σ σ⁻¹
    rw [mul_inv_cancel, cocycles₁_map_one] at this
    exact eq_neg_of_add_eq_zero_left this.symm
  rw [h1 (σ⁻¹ * τ) σ, h1 σ⁻¹ τ, map_add, map_add, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, hinv]
  abel

end Conj

universe u
variable {k : Type u} [Field k] {Γ H : Type u} [Group Γ] [Group H] (loc : H →* Γ) (M : Rep.{u} k Γ) (χ : Γ →* kˣ)

lemma ofChar_ρ_apply (ψ : H →* kˣ) (g : H) (t : k) : (ofChar (k := k) ψ).ρ g t = (ψ g : k) * t := rfl

lemma dualTwist_apply (γ : Γ) (f : M.dualTwist χ) (m : M) :
    ((M.dualTwist χ).ρ γ f) m = (χ γ : k) * f (M.ρ γ⁻¹ m) := rfl

lemma ρ_inv_self (γ : Γ) (m : M) : M.ρ γ⁻¹ (M.ρ γ m) = m := by
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

theorem d₁₂_pair_smul_apply (fq : cocycles₁ (Rep.res loc M)) (v₀ : M.dualTwist χ)
    (wq : H → k) (hwq : ∀ g, wq g = ((M.dualTwist χ).ρ (loc g) v₀) (fq g)) (g h : H) :
    (d₁₂ (ofChar (k := k) (χ.comp loc))).hom wq (g, h) =
      - (((M.dualTwist χ).ρ (loc g)) ((M.dualTwist χ).ρ (loc h) v₀ - v₀)) (fq g) := by
  have hfq : (fq (g * h) : M) = M.ρ (loc g) (fq h) + fq g := (mem_cocycles₁_iff fq).1 fq.2 g h
  rw [d₁₂_hom_apply, ofChar_ρ_apply, hwq, hwq, hwq, hfq, map_mul, map_mul, Module.End.mul_apply, MonoidHom.comp_apply]
  dsimp only
  generalize (M.dualTwist χ).ρ (loc h) v₀ = uu
  rw [dualTwist_apply, dualTwist_apply, dualTwist_apply, map_add, ρ_inv_self, map_add uu, LinearMap.sub_apply]
  ring

section Kummer

variable {p : ℕ} [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)

include hζ in
lemma pow_val_mul (a b : ZMod p) : ζ ^ (a.val * b.val) = ζ ^ (a * b).val := by
  rw [ZMod.val_mul]
  conv_lhs => rw [← Nat.mod_add_div (a.val * b.val) p, pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]

include hζ in

lemma algEquiv_apply_zeta (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    σ ζ = ζ ^ ((cycloChar p σ : ZMod p)).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    (σ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) (t := hζ.toRootsOfUnity.val) hζ.toRootsOfUnity.2
  exact h

include hζ in

lemma zmod_eq_of_pow_val_eq {a b : ZMod p} (h : ζ ^ a.val = ζ ^ b.val) : a = b := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

variable {G : Type} [Group G] (πF : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* G)
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (B : Rep ℤ G)
  (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
    κ (B.ρ (πF γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
  (β : B →+ M.dualTwist (cycloChar p))
  (hκβ : ∀ (b : B) (m : M), ((Additive.toMul (κ b m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
    ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val)

lemma coe_toMul_ρ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : Additive (AlgebraicClosure ℚ)ˣ) :
    ((Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ a) : (AlgebraicClosure ℚ)ˣ) :
      AlgebraicClosure ℚ) = γ ((Additive.toMul a : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) := by
  rfl

include hζ hκβ in

lemma coe_ρ_kappa (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M) :
    ((Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m)) : (AlgebraicClosure ℚ)ˣ) :
      AlgebraicClosure ℚ) = ζ ^ ((cycloChar p γ : ZMod p) * ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val := by
  rw [coe_toMul_ρ, hκβ, map_pow, algEquiv_apply_zeta ζ hζ, ← pow_mul, pow_val_mul ζ hζ]

include hζ hκeq hκβ in

theorem beta_equivariant (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) :
    β (B.ρ (πF γ) b) = (M.dualTwist (cycloChar p)).ρ γ (β b) := by
  apply LinearMap.ext
  intro m
  have key : ∀ m', ((β (B.ρ (πF γ) b) : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (M.ρ γ m') =
      (cycloChar p γ : ZMod p) * ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m' := by
    intro m'
    apply zmod_eq_of_pow_val_eq ζ hζ
    rw [← hκβ, hκeq, coe_ρ_kappa ζ hζ M B κ β hκβ]
  have := key (M.ρ γ⁻¹ m)
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  rw [this]
  rfl

variable (q : ℕ) [Fact q.Prime] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (κq : B →+ M →+ Additive (PadicAlgCl q)ˣ)
  (hκq : ∀ (b : B) (m : M), Additive.toMul (κq b m) =
    Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))

include hζ hκβ hκq in

theorem coe_kappaq (b : B) (m : M) :
    ((Additive.toMul (κq b m) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ ((((M.dualTwist (cycloChar p)).ρ σ (β b) : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val := by
  rw [hκq, Units.coe_map, MonoidHom.coe_coe, coe_ρ_kappa ζ hζ M B κ β hκβ, map_pow]
  rfl

end Kummer

section Local

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) [Fact (((q : Nat.Primes) : ℕ)).Prime]
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (w : HeightOneSpectrum (𝓞 ↥F))
  (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
  (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
  (hΦπ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))

noncomputable abbrev AqS : Rep ℤ (primeLocalGaloisGroup q) :=
  (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))

noncomputable abbrev Xw : Rep ℤ ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) :=
  Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ

noncomputable abbrev ιq : Xw F w →+ AqS S q := (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive

include hΦπ in

theorem iota_equivariant (τ : primeLocalGaloisGroup q) (x : Xw F w) :
    ιq S q F w Φ ((Xw F w).ρ (π τ) x) = (AqS S q).ρ τ (ιq S q F w Φ x) := by
  apply Additive.toMul.injective
  apply Units.ext
  change Φ (((π τ) • (Additive.toMul x : (w.adicCompletion ↥F)ˣ) : (w.adicCompletion ↥F)ˣ) : w.adicCompletion ↥F) =
    (((show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) •
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul x : (w.adicCompletion ↥F)ˣ) : (PadicAlgCl q)ˣ)
      : (PadicAlgCl q)ˣ) : PadicAlgCl q)
  rw [NumberField.PlaceDecomp.coe_smul_units, hΦπ]
  rfl

end Local

section RootsGeneric
variable {K : Type} [Field K] {p : ℕ} [Fact p.Prime] {z : K} (hz : IsPrimitiveRoot z p)

include hz in
lemma pow_val_mul' (a b : ZMod p) : z ^ (a.val * b.val) = z ^ (a * b).val := by
  rw [ZMod.val_mul]
  conv_lhs => rw [← Nat.mod_add_div (a.val * b.val) p, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

include hz in
lemma zmod_eq_of_pow_val_eq' {a b : ZMod p} (h : z ^ a.val = z ^ b.val) : a = b := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  exact ZMod.val_injective p (hz.pow_inj (ZMod.val_lt a) (ZMod.val_lt b) h)

end RootsGeneric

section KappaQ

variable {p : ℕ} [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  {G : Type} [Group G]
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (B : Rep ℤ G)
  (hB : ∀ b : B, p • b = 0)
  (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
  (β : B →+ M.dualTwist (cycloChar p))
  (hκβ : ∀ (b : B) (m : M), ((Additive.toMul (κ b m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
    ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val)
  (q : ℕ) [Fact q.Prime] (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (κq : B →+ M →+ Additive (PadicAlgCl q)ˣ)
  (hκqζ : ∀ (b : B) (m : M), ((Additive.toMul (κq b m) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ ((((M.dualTwist (cycloChar p)).ρ σ (β b) : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val)

include hζ hB hκ hκβ hκqζ in

theorem exists_kappaq_eq (c : B →+ Additive (PadicAlgCl q)ˣ) : ∃ m : M, ∀ b, κq b m = c b := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hinj : Function.Injective (padicEmbedding q) := (padicEmbedding q).toRingHom.injective
  have hζq : IsPrimitiveRoot (padicEmbedding q ζ) p := hζ.map_of_injective hinj
  have hζ0 : ζ ≠ 0 := hζ.ne_zero (Fact.out : p.Prime).ne_zero

  have hroot : ∀ b : B, ∃ i : ℕ, padicEmbedding q ζ ^ i = ((Additive.toMul (c b) : (PadicAlgCl q)ˣ) : PadicAlgCl q) := by
    intro b
    have hp1 : ((Additive.toMul (c b) : (PadicAlgCl q)ˣ) : PadicAlgCl q) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, ← toMul_nsmul, ← map_nsmul, hB, map_zero]
      rfl
    obtain ⟨i, -, h⟩ := hζq.eq_pow_of_pow_eq_one hp1
    exact ⟨i, h⟩
  choose j hj using hroot

  let cfun : B → (AlgebraicClosure ℚ)ˣ := fun b => Units.mk0 (ζ ^ j b) (pow_ne_zero _ hζ0)
  have hcfun : ∀ b, padicEmbedding q ((cfun b : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ((Additive.toMul (c b) : (PadicAlgCl q)ˣ) : PadicAlgCl q) := fun b => by
    change padicEmbedding q (ζ ^ j b) = _
    rw [map_pow, hj]
  have hcfun_inj : ∀ u v : (AlgebraicClosure ℚ)ˣ,
      padicEmbedding q (u : AlgebraicClosure ℚ) = padicEmbedding q (v : AlgebraicClosure ℚ) → u = v :=
    fun u v h => Units.ext (hinj h)
  let c' : B →+ Additive (AlgebraicClosure ℚ)ˣ :=
    { toFun := fun b => Additive.ofMul (cfun b)
      map_zero' := by
        apply Additive.toMul.injective
        apply hcfun_inj
        change padicEmbedding q ((cfun 0 : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) = padicEmbedding q ((1 : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ)
        rw [hcfun, map_zero, Units.val_one, map_one]
        rfl
      map_add' := fun b b' => by
        apply Additive.toMul.injective
        apply hcfun_inj
        change padicEmbedding q ((cfun (b + b') : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
          padicEmbedding q (((cfun b * cfun b' : (AlgebraicClosure ℚ)ˣ)) : AlgebraicClosure ℚ)
        rw [hcfun, map_add, Units.val_mul, map_mul, hcfun, hcfun]
        rfl }
  obtain ⟨m', hm', -⟩ := hκ c'

  have hjβ : ∀ b, padicEmbedding q ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m').val =
      ((Additive.toMul (c b) : (PadicAlgCl q)ˣ) : PadicAlgCl q) := by
    intro b
    rw [← hcfun, ← map_pow, ← hκβ, hm']
    rfl

  refine ⟨M.ρ σ ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p) • m'), fun b => ?_⟩
  apply Additive.toMul.injective
  apply Units.ext
  rw [hκqζ, ← hjβ]
  congr 2
  change (cycloChar p σ : ZMod p) * ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M)
      (M.ρ σ⁻¹ (M.ρ σ ((((cycloChar p σ)⁻¹ : (ZMod p)ˣ) : ZMod p) • m'))) = _
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_smul, smul_eq_mul,
    ← mul_assoc, Units.mul_inv, one_mul]

end KappaQ

section KumMap

variable {p : ℕ} [Fact p.Prime] (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) (q : Nat.Primes) [Fact ((q : ℕ)).Prime]

noncomputable abbrev Aq : Rep ℤ (primeLocalGaloisGroup q) :=
  (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))

lemma pow_val_add' {K : Type} [Field K] {z : K} (hz : IsPrimitiveRoot z p) (a b : ZMod p) :
    z ^ (a.val + b.val) = z ^ (a + b).val := by
  rw [ZMod.val_add]
  conv_lhs => rw [← Nat.mod_add_div (a.val + b.val) p, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

lemma pow_val_mul'' {K : Type} [Field K] {z : K} (hz : IsPrimitiveRoot z p) (a b : ZMod p) :
    z ^ (a.val * b.val) = z ^ (a * b).val := by
  rw [ZMod.val_mul]
  conv_lhs => rw [← Nat.mod_add_div (a.val * b.val) p, pow_add, pow_mul, hz.pow_eq_one, one_pow, mul_one]

noncomputable def zetaq : (PadicAlgCl q)ˣ :=
  Units.mk0 (padicEmbedding q ζ) (by
    haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
    exact (hζ.map_of_injective (padicEmbedding (q : ℕ)).toRingHom.injective).ne_zero (Fact.out : p.Prime).ne_zero)

lemma coe_zetaq : ((zetaq ζ hζ q : (PadicAlgCl q)ˣ) : PadicAlgCl q) = padicEmbedding q ζ := rfl

noncomputable def kum : ZMod p →+ Aq q where
  toFun t := Additive.ofMul (zetaq ζ hζ q ^ t.val)
  map_zero' := by rw [ZMod.val_zero, pow_zero]; rfl
  map_add' t t' := by
    apply Additive.toMul.injective
    apply Units.ext
    change ((zetaq ζ hζ q ^ (t + t').val : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      ((zetaq ζ hζ q ^ t.val * zetaq ζ hζ q ^ t'.val : (PadicAlgCl q)ˣ) : PadicAlgCl q)
    have hζq : IsPrimitiveRoot (padicEmbedding q ζ) p := hζ.map_of_injective (padicEmbedding (q : ℕ)).toRingHom.injective
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, coe_zetaq, ← pow_add,
      pow_val_add' hζq]

lemma coe_kum (t : ZMod p) : ((Additive.toMul (kum ζ hζ q t) : (PadicAlgCl q)ˣ) : PadicAlgCl q) = padicEmbedding q ζ ^ t.val := by
  change ((zetaq ζ hζ q ^ t.val : (PadicAlgCl q)ˣ) : PadicAlgCl q) = _
  rw [Units.val_pow_eq_pow_val, coe_zetaq]

include hζ in

lemma gal_zetaq (τ : primeLocalGaloisGroup q) :
    (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (padicEmbedding q ζ) =
      padicEmbedding q ζ ^ ((cycloChar p (primeLocalToGlobal q τ) : ZMod p)).val := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h1 : padicEmbedding (q : ℕ) (primeLocalToGlobal q τ ζ) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (padicEmbedding q ζ) :=
    padicEmbedding_localGaloisToGlobal (q : ℕ) τ ζ
  rw [← h1]
  have h2 := modularCyclotomicCharacter.spec (AlgebraicClosure ℚ) (card_rootsOfUnity_eq_self p)
    ((primeLocalToGlobal q τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ)
    (t := hζ.toRootsOfUnity.val) hζ.toRootsOfUnity.2
  have h2' : ((primeLocalToGlobal q τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ζ =
      ζ ^ ((cycloChar p (primeLocalToGlobal q τ) : ZMod p)).val := h2
  change padicEmbedding (q : ℕ) ((primeLocalToGlobal q τ : AlgebraicClosure ℚ ≃+* AlgebraicClosure ℚ) ζ) = _
  rw [h2', map_pow]

theorem kum_equivariant (τ : primeLocalGaloisGroup q) (t : ZMod p) :
    kum ζ hζ q ((ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))).ρ τ t) = (Aq q).ρ τ (kum ζ hζ q t) := by
  have hζq : IsPrimitiveRoot (padicEmbedding q ζ) p := hζ.map_of_injective (padicEmbedding (q : ℕ)).toRingHom.injective
  apply Additive.toMul.injective
  apply Units.ext
  change ((Additive.toMul (kum ζ hζ q (((cycloChar p).comp (primeLocalToGlobal q) τ : ZMod p) * t)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
    (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) ((Additive.toMul (kum ζ hζ q t) : (PadicAlgCl q)ˣ) : PadicAlgCl q)
  rw [coe_kum, coe_kum, map_pow, gal_zetaq ζ hζ q, ← pow_mul, MonoidHom.comp_apply, pow_val_mul'' hζq]

end KumMap

section BridgeMore

variable {k k' : Type u} [CommRing k] [CommRing k'] {H D : Type u} [Group H] [Group D] (π : H →* D)
  {R P B : Rep.{u} k D} (f : R ⟶ P) (g : P ⟶ B) {X : Rep.{u} k D} {A : Rep.{u} k H} (ι : X →+ A)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  {M : Rep.{u} k' H} (κ' : B →+ M →+ A)
  (hκeq : ∀ (h : H) (b : B) (m : M), κ' (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ' b m))
  (hsep : ∀ m m' : M, (∀ b, κ' b m = κ' b m') → m = m')

include hιeq in

theorem cob_apply_f (aw : R ⟶ X) (ψ : (ihom (Rep.res π P)).obj A) (hψ : ∀ r : R, ev π P A ψ (f.hom r) = ι (aw.hom r))
    (h : H) (r : R) : cob π P A ψ h (f.hom r) = 0 := by
  rw [cob_apply, ← Rep.hom_comm_apply f, hψ, hψ, Rep.hom_comm_apply aw, map_inv, ← hιeq, ← Module.End.mul_apply,
    ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply, sub_self]

theorem exists_factor {A' : Type} [AddCommGroup A'] (hfg : ∀ x : P, g.hom x = 0 → ∃ r, f.hom r = x)
    (hg : Function.Surjective g.hom) (c : P →+ A') (hc : ∀ r : R, c (f.hom r) = 0) :
    ∃ cB : B →+ A', ∀ x : P, cB (g.hom x) = c x := by
  classical
  have hker : ∀ y y' : P, g.hom y = g.hom y' → c y = c y' := by
    intro y y' hyy'
    have h0 : g.hom (y - y') = 0 := by rw [map_sub, hyy', sub_self]
    obtain ⟨r, hr⟩ := hfg _ h0
    have := hc r
    rw [hr, map_sub, sub_eq_zero] at this
    exact this
  have hs : ∀ b, g.hom (Function.surjInv hg b) = b := Function.surjInv_eq hg
  refine ⟨AddMonoidHom.mk' (fun b => c (Function.surjInv hg b)) (fun b b' => ?_), fun x => hker _ _ (hs _)⟩
  rw [← map_add]
  exact hker _ _ (by rw [hs, map_add, hs, hs])

include hκeq in
lemma kappa_ρ (h : H) (b : B) (m : M) : κ' b (M.ρ h m) = A.ρ h (κ' (B.ρ (π h⁻¹) b) m) := by
  rw [← hκeq, map_inv, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

include hκeq hsep in

theorem mem_cocycles₁_of_forall_kappa (hg : Function.Surjective g.hom) (ψ : (ihom (Rep.res π P)).obj A) (n : H → M)
    (hn : ∀ (h : H) (x : P), κ' (g.hom x) (n h) = cob π P A ψ h x) : n ∈ cocycles₁ M := by
  rw [mem_cocycles₁_iff]
  intro h₁ h₂
  apply hsep
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [map_add, hn, kappa_ρ π κ' hκeq, ← Rep.hom_comm_apply g, hn, hn]
  simp only [cob_apply, map_mul, mul_inv_rev, Module.End.mul_apply, map_sub, map_inv]
  abel

end BridgeMore

section Specific

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) [Fact (((q : Nat.Primes) : ℕ)).Prime]
  (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p)
  (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (w : HeightOneSpectrum (𝓞 ↥F))
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
  (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
  (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
  (B : Rep.{0} ℤ (↥F ≃ₐ[ℚ] ↥F))
  (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
  (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
    κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
  (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
  (β : B →+ M.dualTwist (cycloChar p))
  (hκβ : ∀ (b : B) (m : M), ((Additive.toMul (κ b m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
    ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val)
  (κq : B →+ M →+ Additive (PadicAlgCl q)ˣ)
  (hκq : ∀ (b : B) (m : M), Additive.toMul (κq b m) =
    Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
      (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))

include hζ hκ hκβ hκq in

theorem kappaq_sep (m m' : M) (h : ∀ b, κq b m = κq b m') : m = m' := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζq : IsPrimitiveRoot (padicEmbedding q ζ) p := hζ.map_of_injective (padicEmbedding (q : ℕ)).toRingHom.injective
  have h1 : ∀ b, ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (M.ρ σ⁻¹ m) =
      ((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (M.ρ σ⁻¹ m') := by
    intro b
    have := congrArg (fun a : Additive (PadicAlgCl q)ˣ => ((Additive.toMul a : (PadicAlgCl q)ˣ) : PadicAlgCl q)) (h b)
    simp only [coe_kappaq ζ hζ M B κ β hκβ q σ κq hκq] at this
    have h2 := zmod_eq_of_pow_val_eq' hζq this
    change (cycloChar p σ : ZMod p) * _ = (cycloChar p σ : ZMod p) * _ at h2
    exact mul_left_cancel₀ (Units.ne_zero _) h2
  have h3 : ∀ b, κ b (M.ρ σ⁻¹ m) = κ b (M.ρ σ⁻¹ m') := by
    intro b
    apply Additive.toMul.injective
    apply Units.ext
    rw [hκβ, hκβ, h1]
  obtain ⟨m₀, -, huniq⟩ := hκ ((κ.flip) (M.ρ σ⁻¹ m'))
  have e1 : M.ρ σ⁻¹ m = m₀ := huniq _ (fun b => h3 b)
  have e2 : M.ρ σ⁻¹ m' = m₀ := huniq _ (fun b => rfl)
  have : M.ρ σ⁻¹ m = M.ρ σ⁻¹ m' := e1.trans e2.symm
  have := congrArg (M.ρ σ) this
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply,
    ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this

include hζ hπ hκeq hκβ hκq in

theorem kappaq_equivariant (τ : primeLocalGaloisGroup q) (b : B) (m : M) :
    κq ((Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype B).ρ (π τ) b) ((Rep.res (primeLocalToGlobal q) M).ρ τ m) =
      (AqS S q).ρ τ (κq b m) := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have hζq : IsPrimitiveRoot (padicEmbedding q ζ) p := hζ.map_of_injective (padicEmbedding (q : ℕ)).toRingHom.injective
  apply Additive.toMul.injective
  apply Units.ext
  change ((Additive.toMul (κq (B.ρ ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) b) (M.ρ (primeLocalToGlobal q τ) m)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
    (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) ((Additive.toMul (κq b m) : (PadicAlgCl q)ˣ) : PadicAlgCl q)
  rw [coe_kappaq ζ hζ M B κ β hκβ q σ κq hκq, coe_kappaq ζ hζ M B κ β hκβ q σ κq hκq, hπ,
    beta_equivariant ζ hζ (AlgEquiv.restrictNormalHom ↥F) M B κ hκeq β hκβ, map_pow, gal_zetaq ζ hζ (q : Nat.Primes), ← pow_mul,
    pow_val_mul'' hζq, ← Module.End.mul_apply, ← map_mul, show σ * (σ⁻¹ * primeLocalToGlobal q τ * σ) = primeLocalToGlobal q τ * σ by group,
    map_mul, Module.End.mul_apply, dualTwist_apply, ρ_inv_self]

variable {S q F w σ π}

theorem conj_mem_fixingSubgroup (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hγ : γ ∈ F.fixingSubgroup)
    (σ' : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : σ'⁻¹ * γ * σ' ∈ F.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff] at hγ ⊢
  intro y hy
  have hy' : σ' y ∈ F := by
    have := AlgEquiv.restrictNormal_commutes σ' ↥F ⟨y, hy⟩
    change ((σ'.restrictNormal ↥F ⟨y, hy⟩ : ↥F) : AlgebraicClosure ℚ) = σ' y at this
    rw [← this]
    exact Subtype.mem _
  change σ'⁻¹ (γ (σ' y)) = y
  rw [hγ _ hy', ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]

include hπ in

theorem pi_eq_one_of_mem (s : primeLocalGaloisGroup q) (hs : primeLocalToGlobal q s ∈ F.fixingSubgroup) : π s = 1 := by
  have hconj : σ⁻¹ * primeLocalToGlobal q s * σ ∈ F.fixingSubgroup := conj_mem_fixingSubgroup _ hs σ
  apply Subtype.ext
  rw [hπ, OneMemClass.coe_one]

  rw [IntermediateField.mem_fixingSubgroup_iff] at hconj
  apply AlgEquiv.ext
  intro y
  apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
  change algebraMap ↥F (AlgebraicClosure ℚ) ((σ⁻¹ * primeLocalToGlobal q s * σ).restrictNormal ↥F y) = algebraMap ↥F (AlgebraicClosure ℚ) y
  rw [AlgEquiv.restrictNormal_commutes]
  exact hconj y y.2

include hπ in

theorem isLevelConstant₁_comp_pi {Y : Type} (φ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) → Y) :
    IsLevelConstant₁ (primeLocalToGlobal q) (fun g => φ (π g)) :=
  ⟨F, inferInstance, fun g s hs => by beta_reduce; rw [map_mul, pi_eq_one_of_mem hπ s hs, mul_one]⟩

theorem dualTwist_ρ_ny_eq (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p)))
    (hny : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)))
    (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hγ : γ ∈ F.fixingSubgroup) (τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (M.dualTwist (cycloChar p)).ρ γ (ny τ) = ny τ := by
  have hγ1 : AlgEquiv.restrictNormalHom ↥F γ = 1 := by
    rw [IntermediateField.mem_fixingSubgroup_iff] at hγ
    apply AlgEquiv.ext
    intro y
    apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
    change algebraMap ↥F (AlgebraicClosure ℚ) (γ.restrictNormal ↥F y) = algebraMap ↥F (AlgebraicClosure ℚ) y
    rw [AlgEquiv.restrictNormal_commutes]
    exact hγ y y.2
  have h1 := (mem_cocycles₁_iff ny).1 ny.2 γ τ
  rw [hny (γ * τ), hny γ, map_mul, hγ1, one_mul, cocycles₁_map_one, map_zero, add_zero, ← hny] at h1
  exact h1.symm

theorem isLevelConstant₁_w (n : cocycles₁ B) (ny : cocycles₁ (M.dualTwist (cycloChar p)))
    (hny : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)))
    (fq : cocycles₁ (Rep.res (primeLocalToGlobal q) M)) (hfq : IsLevelConstant₁ (primeLocalToGlobal q) (⇑fq))
    (wq : primeLocalGaloisGroup q → ZMod p)
    (hwq : ∀ g, wq g = (((M.dualTwist (cycloChar p)).ρ (primeLocalToGlobal q g) (ny σ) : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (fq g)) :
    IsLevelConstant₁ (primeLocalToGlobal q) wq := by
  obtain ⟨F₁, hF₁, h₁⟩ := hfq
  haveI := hF₁
  refine ⟨F ⊔ F₁, inferInstance, fun g s hs => ?_⟩
  rw [hwq, hwq]
  rw [h₁ g s (IntermediateField.fixingSubgroup_antitone le_sup_right hs), map_mul, map_mul, Module.End.mul_apply,
    dualTwist_ρ_ny_eq M B β n ny hny _ (IntermediateField.fixingSubgroup_antitone le_sup_left hs) σ]

theorem isLevelConstant₁_of_forall_eq {Y : Type} {f f' : primeLocalGaloisGroup q → Y}
    (hf : IsLevelConstant₁ (primeLocalToGlobal q) f) (h : ∀ g, f' g = f g) : IsLevelConstant₁ (primeLocalToGlobal q) f' := by
  obtain ⟨F₁, hF₁, h₁⟩ := hf
  exact ⟨F₁, hF₁, fun g s hs => by rw [h, h, h₁ g s hs]⟩

end Specific

section ExactHelper
variable {k : Type u} [CommRing k] {D : Type u} [Group D] {T : ShortComplex (Rep.{u} k D)}

theorem exact_fg (hT : T.ShortExact) (y : T.X₂) (hy : T.g.hom y = 0) : ∃ r : T.X₁, T.f.hom r = y :=
  (ShortComplex.moduleCat_exact_iff _).1 (hT.exact.map (forget₂ (Rep k D) (ModuleCat k))) y hy

end ExactHelper

def toIntLinearMapOfModules {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) : @LinearMap ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW :=
  @LinearMap.mk ℤ ℤ _ _ (RingHom.id ℤ) V W _ _ instV instW ⟨u, u.map_add⟩ (fun c m => by
    letI := instV
    letI := instW
    exact map_intCast_smul u ℤ ℤ c m)

theorem toIntLinearMapOfModules_apply {V W : Type} [AddCommGroup V] [AddCommGroup W] (instV : Module ℤ V) (instW : Module ℤ W)
    (u : V →+ W) (m : V) : @DFunLike.coe _ _ _ (@LinearMap.instFunLike ℤ ℤ V W _ _ _ _ instV instW (RingHom.id ℤ))
      (toIntLinearMapOfModules instV instW u) m = u m := rfl

end BridgeCup
p2m_reactivate "P2MW.S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant.BridgeCup"

set_option maxHeartbeats 80000000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S)
    [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (ζ : AlgebraicClosure ℚ) (hζ : IsPrimitiveRoot ζ p) :
    ∃ u : (ZMod p)ˣ,
    ∀ (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))

    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (_ : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (_ : Continuous Φ)
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (_ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (_ : Function.Surjective π)
    (_ : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))

    (T : ShortComplex (Rep ℤ (↥F ≃ₐ[ℚ] ↥F))) (hT : T.ShortExact)
    (hTD : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).ShortExact)
    (_ : ∀ b : T.X₃, p • b = 0)
    (κ : T.X₃ →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (_ : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : T.X₃) (m : M),
      κ (T.X₃.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (_ : ∀ c : T.X₃ →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    (β : T.X₃ →+ M.dualTwist (cycloChar p))
    (_ : ∀ (b : T.X₃) (m : M), ((Additive.toMul (κ b m) : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) =
      ζ ^ (((β b : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) m).val)
    (κq : T.X₃ →+ M →+ Additive (PadicAlgCl q)ˣ)
    (_ : ∀ (b : T.X₃) (m : M), Additive.toMul (κq b m) =
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
        (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))

    (Λq : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M))
    (_ : IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.f) ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map T.g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)

    (aw : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₁ ⟶ Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (n : cocycles₁ T.X₃) (ny : cocycles₁ (M.dualTwist (cycloChar p)))
    (_ : ∀ γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, ny γ = β (n (AlgEquiv.restrictNormalHom ↥F γ)))

    (fq : cocycles₁ (Rep.res (primeLocalToGlobal q) M)) (_ : (H1π _).hom fq = Λq aw)
    (hfq : IsLevelConstant₁ (primeLocalToGlobal q) (⇑fq))
    (gq : cocycles₁ (Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))))
    (_ : ∀ τ : primeLocalGaloisGroup q, gq τ = ny (primeLocalToGlobal q τ))
    (e : levelCocycles₂ (primeLocalToGlobal q) (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
    (_ : ∀ st, (e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) st =
      cupCochain (Module.Dual.eval (ZMod p) M :
          Rep.res (primeLocalToGlobal q) M →ₗ[ZMod p]
            Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p)) →ₗ[ZMod p] (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q))))
        (⇑fq) (⇑gq) st)

    (E : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (_ : ∀ g h : primeLocalGaloisGroup q, ((Additive.toMul ((E : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) : (PadicAlgCl q)ˣ) : PadicAlgCl q) =
      padicEmbedding q ζ ^ (((e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h) : ZMod p).val))
    (x : cocycles₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ))
    (_ : (H2π (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom x = (groupCohomology.map (MonoidHom.id ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) aw 2).hom
      ((groupCohomology.δ hTD 1 2 rfl).hom
        ((groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1).hom ((H1π T.X₃).hom n))))
    (X : levelCocycles₂ (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    (_ : ∀ g h : primeLocalGaloisGroup q, Additive.toMul ((X : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) (g, h)) =
      Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul ((x : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) × ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) → Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) (π g, π h)))),
    continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) X =
      (((u : ZMod p).val : ℤ)) • continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) E := by
  classical
  refine ⟨-1, ?_⟩
  intro M F _instNF _instG w σ Φ hΦF hΦc π hπ hπsurj hΦπ T hT hTD hB κ hκeq hκ β hκβ κq hκq Λq hΛ aw n ny hny fq hfqpin hfq gq hgq
    e he E hE x hx X hX
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩

  have hζq : IsPrimitiveRoot (padicEmbedding q ζ) p := hζ.map_of_injective (padicEmbedding ((q : Nat.Primes) : ℕ)).toRingHom.injective

  have hιeq : ∀ (τ : primeLocalGaloisGroup q) (x : (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)), ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) ((Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ).ρ (π τ) x) = (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) x) :=
    BridgeCup.iota_equivariant S q F w Φ π hΦπ
  have hκqζ := BridgeCup.coe_kappaq ζ hζ M T.X₃ κ β hκβ ((q : Nat.Primes) : ℕ) σ κq hκq
  have hsep : ∀ m m' : M, (∀ b, κq b m = κq b m') → m = m' := BridgeCup.kappaq_sep S q ζ hζ M F σ T.X₃ κ hκ β hκβ κq hκq
  have hκqeq : ∀ (h : primeLocalGaloisGroup q) (b : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₃) (m : Rep.res (primeLocalToGlobal q) M),
      κq ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₃.ρ (π h) b) ((Rep.res (primeLocalToGlobal q) M).ρ h m) = (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ h (κq b m) :=
    BridgeCup.kappaq_equivariant S q ζ hζ M F w σ π hπ T.X₃ κ hκeq β hκβ κq hκq

  have hg_surj : Function.Surjective (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g.hom := (Rep.epi_iff_surjective (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g).1 hTD.epi_g
  have hf_inj : Function.Injective (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f.hom := (Rep.mono_iff_injective (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f).1 hTD.mono_f
  have hfg : ∀ y : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂, (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g.hom y = 0 → ∃ r : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₁, (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f.hom r = y := fun y hy => BridgeCup.exact_fg hTD y hy
  have hgf : ∀ r : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₁, (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g.hom ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f.hom r) = 0 := fun r => by
    have := congrArg (fun φ => φ.hom r) (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).zero
    exact this

  obtain ⟨ψa, hψa⟩ := BridgeCup.exists_extension (A := Additive (PadicAlgCl q)ˣ)
    (AddMonoidHom.mk' (fun r => (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f.hom r) (fun a b => map_add _ a b)) hf_inj
    (AddMonoidHom.mk' (fun r => ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (aw.hom r)) (fun a b => by beta_reduce; exact (congrArg (((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive)) (map_add aw.hom a b)).trans (map_add _ _ _)))
  let ψ₀ : (ihom (Rep.res π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂)).obj (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := BridgeCup.toIntLinearMapOfModules _ _ ψa
  have hψ₀ : ∀ r : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₁, BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ₀ ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f.hom r) = ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (aw.hom r) := fun r => hψa r

  have hnb : ∀ h : primeLocalGaloisGroup q, ∃ m : M, ∀ y : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂, κq ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g.hom y) m = BridgeCup.cob π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ₀ h y := by
    intro h
    obtain ⟨cB, hcB⟩ := BridgeCup.exists_factor (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g hfg hg_surj
      (BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ((d₀₁ ((ihom (Rep.res π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂)).obj (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))).hom ψ₀ h)).toAddMonoidHom
      (fun r => BridgeCup.cob_apply_f (X := (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) hιeq aw ψ₀ hψ₀ h r)
    obtain ⟨m, hm⟩ := BridgeCup.exists_kappaq_eq ζ hζ M T.X₃ hB κ hκ β hκβ ((q : Nat.Primes) : ℕ) σ κq hκqζ cB
    exact ⟨m, fun y => (hm _).trans (hcB y)⟩
  choose nb₀ hnb₀ using hnb
  have hcocy : nb₀ ∈ cocycles₁ (Rep.res (primeLocalToGlobal q) M) :=
    BridgeCup.mem_cocycles₁_of_forall_kappa (M := Rep.res (primeLocalToGlobal q) M) (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g κq hκqeq hsep hg_surj ψ₀ nb₀ hnb₀
  have hΛeq : Λq aw = (H1π _).hom ⟨nb₀, hcocy⟩ := hΛ aw ψ₀ hψ₀ nb₀ hnb₀ hcocy

  rw [hΛeq] at hfqpin
  change H1π _ fq = H1π _ _ at hfqpin
  rw [H1π_eq_iff] at hfqpin
  obtain ⟨m₀, hm₀⟩ := hfqpin
  let Lm : (ihom (Rep.res π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂)).obj (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
    BridgeCup.toIntLinearMapOfModules _ _ (AddMonoidHom.mk' (fun y => κq ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g.hom y) m₀) (fun y y' => by
      beta_reduce
      exact (congrArg (fun b => κq b m₀) (map_add _ y y')).trans
        ((DFunLike.congr_fun (map_add κq _ _) m₀).trans (AddMonoidHom.add_apply _ _ _))))
  let ψ' : (ihom (Rep.res π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂)).obj (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) := ψ₀ + Lm
  have hψ'add : ∀ y, BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' y = BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ₀ y + BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) Lm y :=
    fun y => rfl
  have hLm : ∀ y, BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) Lm y = κq ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g.hom y) m₀ := fun y => rfl
  have hn' : ∀ (h : primeLocalGaloisGroup q) (y : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂), κq ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g.hom y) (fq h) = BridgeCup.cob π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' h y := by
    intro h y
    have hsh := BridgeCup.cob_shift (M := Rep.res (primeLocalToGlobal q) M) (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))) π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).g κq hκqeq ψ₀ ψ' m₀ (fun y => by rw [hψ'add, hLm]; rfl) nb₀ hnb₀ h y
    have e0 := congrFun hm₀ h
    have e1 : nb₀ h + (d₀₁ (Rep.res (primeLocalToGlobal q) M)).hom m₀ h = fq h := by
      rw [e0]
      change nb₀ h + (fq h - nb₀ h) = fq h
      abel
    rw [e1] at hsh
    exact hsh
  have hψ'f : ∀ r : (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₁, BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).f.hom r) = ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (aw.hom r) := fun r => by
    rw [hψ'add, hLm, hψ₀, hgf]
    erw [map_zero κq]
    rw [AddMonoidHom.zero_apply]
    exact add_zero _

  let nD : cocycles₁ (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₃ := mapCocycles₁ (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 _) n
  have hnD : ∀ d, nD d = n (d : ↥F ≃ₐ[ℚ] ↥F) := fun d => rfl
  have hres : (groupCohomology.map (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) 1).hom ((H1π T.X₃).hom n) =
      (H1π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₃).hom nD :=
    H1π_comp_map_apply (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype (𝟙 (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃)) n
  obtain ⟨nt, x₀, b₁, hnt, hx₀, hxrep⟩ := BridgeCup.exists_lift_repr hTD aw nD x _ hres hx

  obtain ⟨wq, hwq⟩ : ∃ wq : primeLocalGaloisGroup q → ZMod p, ∀ g, wq g =
      (((M.dualTwist (cycloChar p)).ρ (primeLocalToGlobal q g) (ny σ) : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (fq g) :=
    ⟨_, fun g => rfl⟩
  let Lb : primeLocalGaloisGroup q → Additive (PadicAlgCl q)ˣ := fun g => ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (b₁ (π g))
  have hLbdef : ∀ g, Lb g = ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (b₁ (π g)) := fun g => rfl
  let Lc : primeLocalGaloisGroup q → Additive (PadicAlgCl q)ˣ := fun g => BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' (nt (π g))
  have hLcdef : ∀ g, Lc g = BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' (nt (π g)) := fun g => rfl
  let Lw : primeLocalGaloisGroup q → Additive (PadicAlgCl q)ˣ := fun g => BridgeCup.kum ζ hζ (q : Nat.Primes) (wq g)
  have hLwdef : ∀ g, Lw g = BridgeCup.kum ζ hζ (q : Nat.Primes) (wq g) := fun g => rfl
  have hLb : IsLevelConstant₁ (primeLocalToGlobal q) Lb :=
    BridgeCup.isLevelConstant₁_of_forall_eq (BridgeCup.isLevelConstant₁_comp_pi hπ (fun d => ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (b₁ d))) hLbdef
  have hLc : IsLevelConstant₁ (primeLocalToGlobal q) Lc :=
    BridgeCup.isLevelConstant₁_of_forall_eq
      (BridgeCup.isLevelConstant₁_comp_pi hπ (fun d => (BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' (nt d) : Additive (PadicAlgCl q)ˣ))) hLcdef
  have hwqL : IsLevelConstant₁ (primeLocalToGlobal q) wq := BridgeCup.isLevelConstant₁_w (σ := σ) M T.X₃ β n ny hny fq hfq wq hwq
  have hLw : IsLevelConstant₁ (primeLocalToGlobal q) Lw :=
    BridgeCup.isLevelConstant₁_of_forall_eq (hwqL.comp (fun t => (BridgeCup.kum ζ hζ (q : Nat.Primes) t : Additive (PadicAlgCl q)ˣ))) hLwdef
  have hL : IsLevelConstant₁ (primeLocalToGlobal q) (Lb + Lc + Lw) := (hLb.add hLc).add hLw

  have key : ∀ g h : primeLocalGaloisGroup q, (X.1 (g, h) : Additive (PadicAlgCl q)ˣ) + (E.1 (g, h) : Additive (PadicAlgCl q)ˣ) =
      ((d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom (Lb + Lc + Lw) (g, h) : Additive (PadicAlgCl q)ˣ) := by
    intro g h

    have hP1 : (X.1 (g, h) : Additive (PadicAlgCl q)ˣ) = ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (x (π g, π h)) :=
      Additive.toMul.injective (hX g h)

    have hP4 : ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) ((d₁₂ (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)).hom b₁ (π g, π h)) = ((d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom Lb (g, h) : Additive (PadicAlgCl q)ˣ) := by
      rw [d₁₂_hom_apply, d₁₂_hom_apply, hLbdef, hLbdef, hLbdef]
      dsimp only
      erw [map_add, map_sub, hιeq, map_mul]
      rfl

    have hLcfun : Lc = fun g => BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' (nt (π g)) := funext hLcdef
    have hP5 := BridgeCup.inflate_psi_d₁₂_sub_d₁₂ π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' nt g h
    rw [← hLcfun] at hP5

    have hP6 : BridgeCup.cob π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' g ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂.ρ (π g) (nt (π h))) =
        κq ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₃.ρ (π g) (n ((π h : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F))) (fq g) := by
      rw [← hn', Rep.hom_comm_apply, hnt, hnD]

    have hP7 : (((M.dualTwist (cycloChar p)).ρ σ (β ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₃.ρ (π g) (n ((π h : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F)))) :
          M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (fq g) =
        (e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h)
          - (d₁₂ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))).hom wq (g, h) := by
      rw [he, cupCochain_apply, BridgeCup.d₁₂_pair_smul_apply (primeLocalToGlobal q) M (cycloChar p) fq (ny σ) wq hwq g h]
      change _ = (((Rep.res (primeLocalToGlobal q) (M.dualTwist (cycloChar p))).ρ g (gq h) : M.dualTwist (cycloChar p)) :
          Module.Dual (ZMod p) M) (fq g) - _
      change (((M.dualTwist (cycloChar p)).ρ σ (β ((Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype T.X₃).ρ (π g)
          (n ((π h : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F)))) : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (fq g) = _
      change (((M.dualTwist (cycloChar p)).ρ σ (β (T.X₃.ρ ((π g : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F)
          (n ((π h : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F)))) : M.dualTwist (cycloChar p)) : Module.Dual (ZMod p) M) (fq g) = _
      rw [hπ g, hπ h, BridgeCup.beta_equivariant ζ hζ (AlgEquiv.restrictNormalHom ↥F) M T.X₃ κ hκeq β hκβ, ← hny,
        ← Module.End.mul_apply, ← map_mul,
        show σ * (σ⁻¹ * primeLocalToGlobal q g * σ) = primeLocalToGlobal q g * σ by group, map_mul, Module.End.mul_apply,
        BridgeCup.smul_apply_conj ny σ (primeLocalToGlobal q h), ← hgq, map_add, LinearMap.add_apply, sub_neg_eq_add]
      rfl

    have hP8 : κq ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₃.ρ (π g) (n ((π h : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F))) (fq g) =
        BridgeCup.kum ζ hζ (q : Nat.Primes) ((e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h))
        - BridgeCup.kum ζ hζ (q : Nat.Primes) ((d₁₂ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))).hom wq (g, h)) := by
      rw [← map_sub, ← hP7]
      apply Additive.toMul.injective
      apply Units.ext
      rw [hκqζ, BridgeCup.coe_kum]
    have hPE : (E.1 (g, h) : Additive (PadicAlgCl q)ˣ) =
        BridgeCup.kum ζ hζ (q : Nat.Primes) ((e : primeLocalGaloisGroup q × primeLocalGaloisGroup q → (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))) (g, h)) := by
      apply Additive.toMul.injective
      apply Units.ext
      exact (hE g h).trans (BridgeCup.coe_kum ζ hζ _ _).symm
    have hPw : BridgeCup.kum ζ hζ (q : Nat.Primes) ((d₁₂ (ofChar (k := ZMod p) ((cycloChar p).comp (primeLocalToGlobal q)))).hom wq (g, h)) =
        ((d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom Lw (g, h) : Additive (PadicAlgCl q)ˣ) := by
      rw [d₁₂_hom_apply, d₁₂_hom_apply, hLwdef, hLwdef, hLwdef, map_add, map_sub, BridgeCup.kum_equivariant]

    have hd : ((d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom (Lb + Lc + Lw) (g, h) : Additive (PadicAlgCl q)ˣ) =
        ((d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom Lb (g, h) : Additive (PadicAlgCl q)ˣ) + ((d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom Lc (g, h) : Additive (PadicAlgCl q)ˣ) +
          ((d₁₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).hom Lw (g, h) : Additive (PadicAlgCl q)ˣ) := by
      erw [map_add, map_add]; rfl
    have hP3 : ((Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive) (aw.hom (x₀ (π g, π h))) = BridgeCup.ev π (T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂ (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψ' ((T.map (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype)).X₂.ρ (π g) (nt (π h)) - nt (π (g * h)) + nt (π g)) := by
      rw [← hψ'f, hx₀, d₁₂_hom_apply, map_mul]
    rw [hd, hP1, hxrep]
    erw [map_add, hP4, hP3, hPE, ← hPw]
    rw [sub_eq_iff_eq_add] at hP5
    erw [hP5, hP6, hP8]
    abel

  have hsum : continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) (X + E) = 0 := by
    rw [continuousH2π_eq_zero_iff, mem_levelCoboundaries₂_iff]
    refine ⟨Lb + Lc + Lw, hL, funext fun gh => ?_⟩
    obtain ⟨g, h⟩ := gh
    rw [← key g h]
    rfl
  have hpE : (p : ℤ) • continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) E = 0 := by
    rw [← map_zsmul]
    convert map_zero (continuousH2π (primeLocalToGlobal q) (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
    apply Subtype.ext
    funext gh
    obtain ⟨g, h⟩ := gh
    have hEp : (Additive.toMul (E.1 (g, h)) : (PadicAlgCl q)ˣ) ^ p = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, hE, ← pow_mul, mul_comm, pow_mul, hζq.pow_eq_one, one_pow, Units.val_one]
    change ((p : ℕ) : ℤ) • (E.1 (g, h) : Additive (PadicAlgCl q)ˣ) = 0
    rw [natCast_zsmul]
    exact (ofMul_pow p (Additive.toMul (E.1 (g, h)) : (PadicAlgCl q)ˣ)).symm.trans (by rw [hEp]; rfl)

  have hval : ((((-1 : (ZMod p)ˣ) : ZMod p)).val : ℤ) = (p : ℤ) - 1 := by
    rw [Units.val_neg, Units.val_one, ZMod.neg_val, if_neg one_ne_zero, ZMod.val_one, Nat.cast_sub (Fact.out : p.Prime).one_lt.le,
      Nat.cast_one]
  rw [hval, sub_smul, one_smul, hpE, zero_sub]
  rw [map_add] at hsum
  exact eq_neg_of_add_eq_zero_left hsum

end S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant
end P2MW
export P2MW.S_NumberField_PlaceDecomp_exists_unit_inflate_map_delta_res_eq_kummer_cup_localBridge_of_isLevelConstant (solution)
