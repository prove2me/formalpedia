-- Prove2me | solution 1 for NumberField.SUnits.locRes_isLocalBridge1_apply_eq_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/d12b2184-26fa-5044-8be5-0628245e934a

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_locRes_isLocalBridge1_apply_eq_of_finite
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open CategoryTheory groupCohomology NumberField IsDedekindDomain ExtCitation
open scoped NumberField.PlaceDecomp

namespace LB1EX

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

def ev (ψ : (ihom (Rep.res π P)).obj A) : P →+ A := LinearMap.toAddMonoidHom (show P →ₗ[k] A from ψ)

lemma ev_add (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ + ψ') x = ev π ψ x + ev π ψ' x := rfl
lemma ev_sub (ψ ψ' : (ihom (Rep.res π P)).obj A) (x : P) : ev π (ψ - ψ') x = ev π ψ x - ev π ψ' x := rfl

noncomputable def cob (ψ : (ihom (Rep.res π P)).obj A) (h : H) : P →+ A := ev π ((d₀₁ ((ihom (Rep.res π P)).obj A)).hom ψ h)

lemma cob_apply (ψ : (ihom (Rep.res π P)).obj A) (h : H) (x : P) :
    cob π ψ h x = A.ρ h (ev π ψ (P.ρ (π h⁻¹) x)) - ev π ψ x := by
  change ev π (((ihom (Rep.res π P)).obj A).ρ h ψ - ψ) x = _
  rw [ev_sub]
  congr 1

lemma ρ_ρ_inv {V : Rep.{0} k D} (d : D) (v : V) : V.ρ d (V.ρ d⁻¹ v) = v := by
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]

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

end hyps

end LB1EX

namespace LB1

noncomputable scoped instance rootableBy_units_algClosure : RootableBy (AlgebraicClosure ℚ)ˣ ℤ :=
  rootableByOfPowLeftSurj _ _ (fun {n} hn => by
    intro c
    rcases Int.natAbs_eq n with hcase | hcase
    ·
      obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (c : AlgebraicClosure ℚ) (Int.natAbs_pos.2 hn)
      have hx0 : x ≠ 0 := by rintro rfl; rw [zero_pow (Int.natAbs_pos.2 hn).ne'] at hx; exact c.ne_zero hx.symm
      refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
      simp only
      rw [hcase, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_mk0, hx]
    · obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq ((c⁻¹ : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) (Int.natAbs_pos.2 hn)
      have hx0 : x ≠ 0 := by rintro rfl; rw [zero_pow (Int.natAbs_pos.2 hn).ne'] at hx; exact (c⁻¹).ne_zero hx.symm
      refine ⟨Units.mk0 x hx0, Units.ext ?_⟩
      simp only
      rw [hcase, zpow_neg, zpow_natCast, Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, Units.val_mk0, hx,
        Units.val_inv_eq_inv_val, inv_inv])

noncomputable scoped instance divisibleBy_additive_units : DivisibleBy (Additive (AlgebraicClosure ℚ)ˣ) ℤ where
  div a n := Additive.ofMul (RootableBy.root (Additive.toMul a) n)
  div_zero a := by rw [RootableBy.root_zero]; rfl
  div_cancel {n} a hn := by
    change Additive.ofMul ((RootableBy.root (Additive.toMul a) n) ^ n) = a
    rw [RootableBy.root_cancel _ hn]
    rfl

scoped instance moduleInjective_additive_units : Module.Injective ℤ (Additive (AlgebraicClosure ℚ)ˣ) :=
  (Module.Baer.of_divisible _).injective

theorem hsmul_int_eq_zsmul {V : Type} [AddCommGroup V] (h : Module ℤ V) (n : ℤ) (x : V) :
    @HSMul.hSMul ℤ V V (@instHSMul ℤ V h.toSMul) n x = n • x := int_smul_eq_zsmul h n x

theorem map_int_smul' {V W : Type} [AddCommGroup V] [AddCommGroup W] {mV : Module ℤ V} {mW : Module ℤ W}
    (ψ : V →+ W) (c : ℤ) (x : V) :
    ψ (@HSMul.hSMul ℤ V V (@instHSMul ℤ V ((@Module.toDistribMulAction ℤ V _ _ mV).toDistribSMul.toSMul)) c x) =
    @HSMul.hSMul ℤ W W (@instHSMul ℤ W ((@Module.toDistribMulAction ℤ W _ _ mW).toDistribSMul.toSMul)) c (ψ x) := by
  have e1 : mV = AddCommGroup.toIntModule V := Subsingleton.elim _ _
  have e2 : mW = AddCommGroup.toIntModule W := Subsingleton.elim _ _
  subst e1
  subst e2
  exact map_zsmul ψ c x

theorem exists_extension {M N Q : Type} [AddCommGroup M] [AddCommGroup N] [AddCommGroup Q] [Module.Injective ℤ Q]
    (f : M →+ N) (hf : Function.Injective f) (χ : M →+ Q) : ∃ ψ : N →+ Q, ∀ x, ψ (f x) = χ x := by
  obtain ⟨h, hh⟩ := Module.Injective.out (R := ℤ) (Q := Q) f.toIntLinearMap hf χ.toIntLinearMap
  exact ⟨h.toAddMonoidHom, hh⟩

def liftHom {k : Type} [CommRing k] {H D : Type} [Group H] [Group D] (π : H →* D) (P : Rep.{0} k D) (A : Rep.{0} k H)
    (ψa : P →+ A) (hs : ∀ (c : k) (x : P), ψa (c • x) = c • ψa x) : (ihom (Rep.res π P)).obj A :=
  { toFun := fun x => ψa x, map_add' := fun x y => ψa.map_add x y, map_smul' := fun c x => hs c x }

theorem ev_liftHom {k : Type} [CommRing k] {H D : Type} [Group H] [Group D] (π : H →* D) (P : Rep.{0} k D) (A : Rep.{0} k H)
    (ψa : P →+ A) (hs : ∀ (c : k) (x : P), ψa (c • x) = c • ψa x) (x : P) :
    LB1EX.ev π (liftHom π P A ψa hs) x = ψa x := rfl

end LB1
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes_isLocalBridge1_apply_eq_of_finite.LB1"

namespace LB1C

theorem conj_cocycle {k G H : Type} [CommRing k] [Group G] [Group H] (l : H →* G) (M : Rep.{0} k G) (σ : G)
    (n : G → M) (hn : n ∈ cocycles₁ M) :
    (fun τ : H => M.ρ σ (n (σ⁻¹ * l τ * σ))) ∈ cocycles₁ (Rep.res l M) ∧
    (fun τ : H => n (l τ)) ∈ cocycles₁ (Rep.res l M) ∧
    ((fun τ : H => M.ρ σ (n (σ⁻¹ * l τ * σ))) - (fun τ : H => n (l τ)) : H → Rep.res l M) ∈ coboundaries₁ (Rep.res l M) := by
  have c := (mem_cocycles₁_iff n).1 hn
  have n1 : n 1 = 0 := cocycles₁_map_one ⟨n, hn⟩

  have key : ∀ g : G, M.ρ σ (n (σ⁻¹ * g * σ)) = n g + (M.ρ g (n σ) - n σ) := by
    intro g
    have hinv : M.ρ σ (n σ⁻¹) = - n σ := cocycles₁_map_inv ⟨n, hn⟩ σ
    have e1 : n (σ⁻¹ * g * σ) = M.ρ (σ⁻¹ * g) (n σ) + n (σ⁻¹ * g) := c _ _
    have e2 : n (σ⁻¹ * g) = M.ρ σ⁻¹ (n g) + n σ⁻¹ := c _ _
    rw [e1, e2, map_add, map_add, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul,
      show σ * (σ⁻¹ * g) = g by group, mul_inv_cancel, map_one, Module.End.one_apply, hinv]
    abel
  have h₂ : (fun τ : H => n (l τ)) ∈ cocycles₁ (Rep.res l M) := by
    rw [mem_cocycles₁_iff]
    intro a b
    show n (l (a * b)) = M.ρ (l a) (n (l b)) + n (l a)
    rw [map_mul]
    exact c _ _
  have hcob : ((fun τ : H => M.ρ σ (n (σ⁻¹ * l τ * σ))) - (fun τ : H => n (l τ)) : H → Rep.res l M) ∈ coboundaries₁ (Rep.res l M) := by
    refine ⟨n σ, ?_⟩
    funext τ
    show M.ρ (l τ) (n σ) - n σ = M.ρ σ (n (σ⁻¹ * l τ * σ)) - n (l τ)
    rw [key]
    abel
  refine ⟨?_, h₂, hcob⟩

  have : (fun τ : H => M.ρ σ (n (σ⁻¹ * l τ * σ))) =
      (fun τ : H => n (l τ)) + ((fun τ : H => M.ρ σ (n (σ⁻¹ * l τ * σ))) - (fun τ : H => n (l τ)) : H → Rep.res l M) := by
    abel
  rw [this]
  exact Submodule.add_mem _ h₂ (coboundaries₁_le_cocycles₁ _ hcob)

theorem H1π_conj_eq {k G H : Type} [CommRing k] [Group G] [Group H] (l : H →* G) (M : Rep.{0} k G) (σ : G)
    (n : G → M) (hn : n ∈ cocycles₁ M)
    (h₁ : (fun τ : H => M.ρ σ (n (σ⁻¹ * l τ * σ))) ∈ cocycles₁ (Rep.res l M)) (h₂ : (fun τ : H => n (l τ)) ∈ cocycles₁ (Rep.res l M)) :
    (H1π (Rep.res l M)).hom ⟨_, h₁⟩ = (H1π (Rep.res l M)).hom ⟨_, h₂⟩ := by
  rw [H1π_eq_iff]
  exact (conj_cocycle l M σ n hn).2.2

end LB1C
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes_isLocalBridge1_apply_eq_of_finite.LB1"

set_option maxHeartbeats 6400000 in

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S)
    [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (heqv : ∀ (τ : primeLocalGaloisGroup q) (x : w.adicCompletion ↥F),
      Φ (π τ • x) = (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) (Φ x))
    {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    [Module.Finite ℤ P] (hB : ∀ b : B, p • b = 0)
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    (κq : B →+ M →+ Additive (PadicAlgCl q)ˣ)
    (hκq : ∀ (b : B) (m : M), Additive.toMul (κq b m) =
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
        (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))
    {ΛE : (R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ) →+ H1 M}
    (hΛE : IsLocalBridge₁ (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)
    {Λq : (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
          Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ) →+
        H1 (Rep.res (primeLocalToGlobal q) M)}
    (hΛq : IsLocalBridge₁ π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)
    (φ : R ⟶ NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)
    (φw : Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R ⟶
      Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
    (hφw : ∀ x : R, Additive.toMul (φw.hom x) =
      Units.map (algebraMap ↥F (w.adicCompletion ↥F) : ↥F →* w.adicCompletion ↥F) (NumberField.SUnits.val ℚ ↥F Sℚ (φ.hom x))) :
    (locRes (extArithLoc S) M (Sum.inr q)).hom (ΛE φ) = Λq φw := by
  classical

  obtain ⟨ψa, hψa⟩ : ∃ ψa : P →+ Additive (AlgebraicClosure ℚ)ˣ, ∀ x : R, ψa (f.hom x) = ιE (φ.hom x) :=
    LB1.exists_extension (AddMonoidHom.mk' (fun x => f.hom x) (fun x y => map_add _ x y)) hf
      (AddMonoidHom.mk' (fun x => ιE (φ.hom x)) (fun x y => by simp only [map_add]))
  let ψ : (ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) P)).obj (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) :=
    LB1.liftHom (AlgEquiv.restrictNormalHom ↥F) P (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ψa
      (fun c x => LB1.map_int_smul' ψa c x)
  have hψ : ∀ x : R, LB1EX.ev (AlgEquiv.restrictNormalHom ↥F) ψ (f.hom x) = ιE (φ.hom x) := hψa

  have hιeqE : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ),
      ιE ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F γ) x) =
        (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (ιE x) := by
    intro γ x
    apply Additive.toMul.injective
    rw [hιE]
    change Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ)
        (NumberField.SUnits.val ℚ ↥F Sℚ ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F γ) x)) =
      γ • Additive.toMul (ιE x)
    rw [NumberField.SUnits.val_rho, hιE]
    ext
    simp only [Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def]
    exact AlgEquiv.restrictNormal_commutes γ ↥F _
  let n : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M := LB1EX.nOf (AlgEquiv.restrictNormalHom ↥F) g κ ψ
  have hn : ∀ γ y, κ (g.hom y) (n γ) = LB1EX.cob (AlgEquiv.restrictNormalHom ↥F) ψ γ y :=
    LB1EX.κ_nOf (AlgEquiv.restrictNormalHom ↥F) f g ιE κ hfg hg hιeqE hκ φ ψ hψ
  have hncoc : n ∈ cocycles₁ M := LB1EX.mem_cocycles₁_of_forall_κ (AlgEquiv.restrictNormalHom ↥F) g κ hg hκeq hκ ψ n hn
  have hΛEφ : ΛE φ = (H1π M).hom ⟨n, hncoc⟩ := hΛE φ ψ hψ n (fun h y => hn h y) hncoc

  let jq : (AlgebraicClosure ℚ)ˣ →* (PadicAlgCl q)ˣ := Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
  let ψqa : P →+ Additive (PadicAlgCl q)ˣ :=
    (MonoidHom.toAdditive jq).comp ((((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ).toAddMonoidHom).comp ψa)
  have hψqa : ∀ y : P, Additive.toMul (ψqa y) = jq (σ • Additive.toMul (ψa y)) := fun y => rfl
  let ψq : (ihom (Rep.res π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).obj P))).obj
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
    LB1.liftHom π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).obj P)
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) ψqa (fun c x => LB1.map_int_smul' ψqa c x)
  have hψq : ∀ x : R, LinearMap.toAddMonoidHom ψq (((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f).hom x) =
      (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (φw.hom x) := by
    intro x
    apply Additive.toMul.injective
    change Additive.toMul (ψqa (f.hom x)) = Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul (φw.hom x))
    rw [hψqa, hψa, hιE]
    erw [hφw]
    ext
    simp only [jq, Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def, hΦF]
    rfl

  let nq : primeLocalGaloisGroup q → M := fun τ => M.ρ σ (n (σ⁻¹ * primeLocalToGlobal q τ * σ))
  have hnq : ∀ (τ : primeLocalGaloisGroup q) (y : (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).obj P),
      κq (((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g).hom y) (nq τ) =
        LinearMap.toAddMonoidHom ((d₀₁ ((ihom (Rep.res π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).obj P))).obj
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))).hom ψq τ) y := by
    intro τ y

    have hγ : ((π τ⁻¹ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
        AlgEquiv.restrictNormalHom ↥F ((σ⁻¹ * primeLocalToGlobal q τ * σ)⁻¹) := by
      rw [map_inv, Subgroup.coe_inv, hπ τ, ← map_inv]
    have hσγ : primeLocalToGlobal q τ * σ = σ * (σ⁻¹ * primeLocalToGlobal q τ * σ) := by group

    have hjq : ∀ (u : (AlgebraicClosure ℚ)ˣ),
        (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) • jq u = jq (primeLocalToGlobal q τ • u) := by
      intro u; ext
      simp only [jq, AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]
      exact (padicEmbedding_localGaloisToGlobal (q : ℕ) _ _).symm

    have hPρ : (((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).obj P).ρ (π τ⁻¹)) y =
        P.ρ (AlgEquiv.restrictNormalHom ↥F ((σ⁻¹ * primeLocalToGlobal q τ * σ)⁻¹)) y := by
      rw [← hγ]; rfl
    have hevq : ∀ z, Additive.toMul (LB1EX.ev π ψq z) = jq (σ • Additive.toMul (ψa z)) := fun z => rfl
    have hev : ∀ z, LB1EX.ev (AlgEquiv.restrictNormalHom ↥F) ψ z = ψa z := fun z => rfl
    have hA : ∀ (γ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : Additive (AlgebraicClosure ℚ)ˣ),
        Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ a) = γ • (Additive.toMul a : (AlgebraicClosure ℚ)ˣ) :=
      fun γ a => rfl
    have hAq : ∀ (a : Additive (PadicAlgCl q)ˣ),
        Additive.toMul (((show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q))).ρ τ a) =
          (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) • (Additive.toMul a : (PadicAlgCl q)ˣ) := fun a => rfl

    apply Additive.toMul.injective
    change Additive.toMul (κq (g.hom y) (M.ρ σ (n (σ⁻¹ * primeLocalToGlobal q τ * σ)))) = Additive.toMul (LB1EX.cob π ψq τ y)
    rw [hκq, LB1EX.ρ_inv_ρ, hn]
    simp only [LB1EX.cob_apply, map_sub, hPρ, hev]
    change jq ((σ • ((σ⁻¹ * primeLocalToGlobal q τ * σ) •
        Additive.toMul (ψa ((P.ρ (AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ)⁻¹)) y)))) /
          (σ • Additive.toMul (ψa y))) =
      (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) •
          jq (σ • Additive.toMul (ψa ((P.ρ (AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ)⁻¹)) y))) /
        jq (σ • Additive.toMul (ψa y))
    rw [map_div, hjq, smul_smul, smul_smul, hσγ]

  obtain ⟨hnqcoc, hnlg, -⟩ := LB1C.conj_cocycle (primeLocalToGlobal q) M σ n hncoc
  have hclass := LB1C.H1π_conj_eq (primeLocalToGlobal q) M σ n hncoc hnqcoc hnlg

  have hΛqφ : Λq φw = (H1π (Rep.res (primeLocalToGlobal q) M)).hom ⟨nq, hnqcoc⟩ := hΛq φw ψq hψq nq hnq hnqcoc
  rw [hΛqφ, hclass, hΛEφ]
  change (groupCohomology.map (extArithLoc S (Sum.inr q)) (𝟙 _) 1).hom ((H1π M).hom ⟨n, hncoc⟩) = _
  rw [groupCohomology.H1π_comp_map_apply]
  rfl

end S_NumberField_SUnits_locRes_isLocalBridge1_apply_eq_of_finite
end P2MW
export P2MW.S_NumberField_SUnits_locRes_isLocalBridge1_apply_eq_of_finite (solution)
