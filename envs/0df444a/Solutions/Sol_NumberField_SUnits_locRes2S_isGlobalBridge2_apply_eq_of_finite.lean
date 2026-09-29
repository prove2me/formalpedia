-- Prove2me | solution 1 for NumberField.SUnits.locRes2S_isGlobalBridge2_apply_eq_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/0c88bef1-26dc-5ae0-824e-9835c0726a62

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge
import Definitions.Def_ExtEndgame_ProductionDatum
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SUnitsModule
import Definitions.Def_M4aHerbrand_SIdeleClassGroup
import Definitions.Def_GroupCohomology_GaloisUnitsInflation
import Definitions.Def_GroupCohomology_ContinuousUnramified
import Definitions.Def_GroupCohomology_LocalBridge
import Definitions.Def_GroupCohomology_GlobalBridge
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Theorems.Thm_IntermediateField_isUnramifiedOutside_normalClosure__721fcc
import Theorems.Thm_NumberField_SUnits_exists_ihom_extension_fixed_of_sLevel_of_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite
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
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1"

namespace EBLB4

theorem conj_sub_eq_d₁₂' {k G : Type} [CommRing k] [Group G] (M : Rep k G) (σ : G) (m : G × G → M) (hm : m ∈ cocycles₂ M) :
    ((fun gh : G × G => M.ρ σ (m (σ⁻¹ * gh.1 * σ, σ⁻¹ * gh.2 * σ))) - m)
      = (d₁₂ M).hom (fun g => m (σ, σ⁻¹ * g * σ) - m (g, σ)) := by
  have c := (mem_cocycles₂_iff m).1 hm
  funext gh
  obtain ⟨g, h⟩ := gh
  rw [Pi.sub_apply, d₁₂_hom_apply, map_sub]
  have e1 : M.ρ g (m (h, σ)) = m (g * h, σ) + m (g, h) - m (g, h * σ) := by
    have := c g h σ
    rw [eq_sub_iff_add_eq, ← this]
  have e2 : M.ρ g (m (σ, σ⁻¹ * h * σ)) = m (g * σ, σ⁻¹ * h * σ) + m (g, σ) - m (g, h * σ) := by
    have := c g σ (σ⁻¹ * h * σ)
    rw [show σ * (σ⁻¹ * h * σ) = h * σ by group] at this
    rw [eq_sub_iff_add_eq, ← this]
  have e3 : M.ρ σ (m (σ⁻¹ * g * σ, σ⁻¹ * h * σ)) = m (g * σ, σ⁻¹ * h * σ) + m (σ, σ⁻¹ * g * σ) - m (σ, σ⁻¹ * (g * h) * σ) := by
    have := c σ (σ⁻¹ * g * σ) (σ⁻¹ * h * σ)
    rw [show σ * (σ⁻¹ * g * σ) = g * σ by group, show σ⁻¹ * g * σ * (σ⁻¹ * h * σ) = σ⁻¹ * (g * h) * σ by group] at this
    rw [eq_sub_iff_add_eq, ← this]
  rw [e1, e2, e3]
  abel

end EBLB4
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1"

namespace EBLB4C

theorem conj_sub_mem_levelCoboundariesS₂ {p : ℕ} (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : m ∈ levelCocyclesS₂ S M) :
    ((fun gh => M.ρ σ (m (σ⁻¹ * gh.1 * σ, σ⁻¹ * gh.2 * σ))) - m) ∈ levelCoboundariesS₂ S M := by
  rw [EBLB4.conj_sub_eq_d₁₂' M σ m hm.1, mem_levelCoboundariesS₂_iff]
  refine ⟨_, ?_, rfl⟩

  obtain ⟨F, hFS, hc⟩ := hm.2
  obtain ⟨hle, hfd, hgal, hNS⟩ := IntermediateField.isUnramifiedOutside_normalClosure S F hFS
  set N : IntermediateField ℚ (AlgebraicClosure ℚ) :=
    IntermediateField.restrictScalars ℚ (IntermediateField.normalClosure ℚ (↥F) (AlgebraicClosure ℚ)) with hN
  haveI : IsGalois ℚ ↥N := hgal
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
  have hnorm : ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ N.fixingSubgroup → σ⁻¹ * s * σ ∈ N.fixingSubgroup := by
    intro s hs
    rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
    intro x hx
    have hσx : σ x ∈ N := by
      have := (IntermediateField.normal_iff_forall_map_le'.mp (IsGalois.to_normal : Normal ℚ ↥N)) σ
      exact this ⟨x, hx, rfl⟩
    show σ⁻¹ (s (σ x)) = x
    rw [hs _ hσx]
    exact σ.symm_apply_apply x
  refine ⟨N, hNS, fun g s hs => ?_⟩
  have hsF : s ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hle hs
  have hsF' : σ⁻¹ * s * σ ∈ F.fixingSubgroup := IntermediateField.fixingSubgroup_antitone hle (hnorm s hs)
  show m (σ, σ⁻¹ * (g * s) * σ) - m (g * s, σ) = m (σ, σ⁻¹ * g * σ) - m (g, σ)
  have h1 : m (σ, σ⁻¹ * (g * s) * σ) = m (σ, σ⁻¹ * g * σ) := by
    have := hc σ (σ⁻¹ * g * σ) 1 (σ⁻¹ * s * σ) F.fixingSubgroup.one_mem hsF'
    rw [mul_one] at this
    rw [show σ⁻¹ * (g * s) * σ = σ⁻¹ * g * σ * (σ⁻¹ * s * σ) by group]
    exact this
  have h2 : m (g * s, σ) = m (g, σ) := by
    have := hc g σ s 1 hsF F.fixingSubgroup.one_mem
    rw [mul_one] at this
    exact this
  rw [h1, h2]

theorem comp_mem_levelCoboundaries₂_of_mem {p : ℕ} (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {H : Type} [Group H] (loc : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (c : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hc : c ∈ levelCoboundariesS₂ S M) :
    (fun hh : H × H => c (loc hh.1, loc hh.2)) ∈ levelCoboundaries₂ loc (Rep.res loc M) := by
  have h := cochainsPullPush₂_mem_levelCoboundaries₂ (rH := MonoidHom.id _) (rG := loc) (A := M) (B := Rep.res loc M)
    loc (fun _ => rfl) LinearMap.id (fun _ _ => rfl) (levelCoboundariesS₂_le_levelCoboundaries₂ S M hc)
  exact h

theorem comp_mem_levelCocycles₂_of_mem {p : ℕ} (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {H : Type} [Group H] (loc : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hx : x ∈ levelCocyclesS₂ S M) :
    (fun hh : H × H => x (loc hh.1, loc hh.2)) ∈ levelCocycles₂ loc (Rep.res loc M) := by
  have h := cochainsPullPush₂_mem_levelCocycles₂ (rH := MonoidHom.id _) (rG := loc) (A := M) (B := Rep.res loc M)
    loc (fun _ => rfl) LinearMap.id (fun _ _ => rfl) (levelCocyclesS₂_le_levelCocycles₂ S M hx)
  exact h

theorem locRes₂S_continuousH2Sπ {p : ℕ} (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {H : Type} [Group H] (loc : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (x : ↥(levelCocyclesS₂ S M)) :
    locRes₂S S M loc (continuousH2Sπ S M x) =
      continuousH2π loc (Rep.res loc M) ⟨fun hh : H × H => (x : _ → M) (loc hh.1, loc hh.2),
        comp_mem_levelCocycles₂_of_mem S M loc x x.2⟩ :=
  rfl

end EBLB4C
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1"

namespace EBLB4C

def conjBy {G : Type} [Group G] (σ : G) : G →* G where
  toFun g := σ⁻¹ * g * σ
  map_one' := by group
  map_mul' a b := by group

@[scoped simp] theorem conjBy_apply {G : Type} [Group G] (σ g : G) : conjBy σ g = σ⁻¹ * g * σ := rfl

theorem conj_mem_levelCocyclesS₂ {p : ℕ} (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : m ∈ levelCocyclesS₂ S M) :
    (fun gh : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) =>
      M.ρ σ (m (σ⁻¹ * gh.1 * σ, σ⁻¹ * gh.2 * σ))) ∈ levelCocyclesS₂ S M := by
  refine ⟨?_, ?_⟩
  ·
    have h := cochainsPullPush₂_mem_cocycles₂ (A := M) (B := M) (conjBy σ) (M.ρ σ) (fun g a => by
        show M.ρ σ (M.ρ (σ⁻¹ * g * σ) a) = M.ρ g (M.ρ σ a)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group) hm.1
    exact h
  ·
    obtain ⟨F, hFS, hc⟩ := hm.2
    obtain ⟨hle, hfd, hgal, hNS⟩ := IntermediateField.isUnramifiedOutside_normalClosure S F hFS
    set N : IntermediateField ℚ (AlgebraicClosure ℚ) :=
      IntermediateField.restrictScalars ℚ (IntermediateField.normalClosure ℚ (↥F) (AlgebraicClosure ℚ)) with hN
    haveI : IsGalois ℚ ↥N := hgal
    haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.instIsAlgClosure ℚ
    haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ _
    have hnorm : ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ N.fixingSubgroup → σ⁻¹ * s * σ ∈ F.fixingSubgroup := by
      intro s hs
      apply IntermediateField.fixingSubgroup_antitone hle
      rw [IntermediateField.mem_fixingSubgroup_iff] at hs ⊢
      intro x hx
      have hσx : σ x ∈ N := by
        have := (IntermediateField.normal_iff_forall_map_le'.mp (IsGalois.to_normal : Normal ℚ ↥N)) σ
        exact this ⟨x, hx, rfl⟩
      show σ⁻¹ (s (σ x)) = x
      rw [hs _ hσx]
      exact σ.symm_apply_apply x
    refine ⟨N, hNS, fun g g' s s' hs hs' => ?_⟩
    show M.ρ σ (m (σ⁻¹ * (g * s) * σ, σ⁻¹ * (g' * s') * σ)) = M.ρ σ (m (σ⁻¹ * g * σ, σ⁻¹ * g' * σ))
    rw [show σ⁻¹ * (g * s) * σ = σ⁻¹ * g * σ * (σ⁻¹ * s * σ) by group,
      show σ⁻¹ * (g' * s') * σ = σ⁻¹ * g' * σ * (σ⁻¹ * s' * σ) by group,
      hc _ _ _ _ (hnorm s hs) (hnorm s' hs')]

theorem continuousH2π_conj_eq {p : ℕ} (S : Finset Nat.Primes)
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    {H : Type} [Group H] (loc : H →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hm : m ∈ levelCocyclesS₂ S M)
    (h₁ : (fun hh : H × H => M.ρ σ (m (σ⁻¹ * loc hh.1 * σ, σ⁻¹ * loc hh.2 * σ))) ∈ levelCocycles₂ loc (Rep.res loc M))
    (h₂ : (fun hh : H × H => m (loc hh.1, loc hh.2)) ∈ levelCocycles₂ loc (Rep.res loc M)) :
    continuousH2π loc (Rep.res loc M) ⟨_, h₁⟩ = continuousH2π loc (Rep.res loc M) ⟨_, h₂⟩ := by
  apply (Submodule.Quotient.eq _).mpr
  rw [Submodule.mem_comap]
  exact comp_mem_levelCoboundaries₂_of_mem S M loc _ (conj_sub_mem_levelCoboundariesS₂ S M σ m hm)

end EBLB4C
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

namespace LB2L

theorem ρ_mul {k G : Type} [CommRing k] [Group G] {V : Rep.{0} k G} (g h : G) (v : V) :
    V.ρ (g * h) v = V.ρ g (V.ρ h v) := by
  rw [map_mul, Module.End.mul_apply]

section generic

variable {Γ Hq D : Type} [Group Γ] [Group Hq] [Group D] (Dw : Subgroup D)
  (πF : Γ →* D) (lg : Hq →* Γ) (π : Hq →* ↥Dw) (σ : Γ)
  (P : Rep.{0} ℤ D) (A : Rep.{0} ℤ Γ) (Aq : Rep.{0} ℤ Hq) (jq : A →+ Aq)
  (ψ : D → (ihom (Rep.res πF P)).obj A)

noncomputable def psiq (d : ↥Dw) : (ihom (Rep.res π ((Rep.resFunctor Dw.subtype).obj P))).obj Aq :=
  LB1.liftHom π ((Rep.resFunctor Dw.subtype).obj P) Aq
    (jq.comp (((A.ρ σ).toAddMonoidHom).comp (LB1EX.ev πF (ψ (d : D))))) (fun c x => LB1.map_int_smul' _ c x)

theorem ev_psiq (d : ↥Dw) (y : P) :
    LB1EX.ev π (psiq Dw πF π σ P A Aq jq ψ d) y = jq (A.ρ σ (LB1EX.ev πF (ψ (d : D)) y)) := rfl

theorem ev_d₁₂_psiq
    (hjq : ∀ (τ : Hq) (u : A), Aq.ρ τ (jq u) = jq (A.ρ (lg τ) u))
    (hπ : ∀ τ : Hq, ((π τ : ↥Dw) : D) = πF (σ⁻¹ * lg τ * σ))
    (τ₁ τ₂ : Hq) (y : P) :
    LB1EX.ev π ((d₁₂ ((ihom (Rep.res π ((Rep.resFunctor Dw.subtype).obj P))).obj Aq)).hom
        ((psiq Dw πF π σ P A Aq jq ψ) ∘ π) (τ₁, τ₂)) y =
      jq (A.ρ σ (LB1EX.ev πF ((d₁₂ ((ihom (Rep.res πF P)).obj A)).hom (ψ ∘ πF) (σ⁻¹ * lg τ₁ * σ, σ⁻¹ * lg τ₂ * σ)) y)) := by
  have hT : ∀ (τ : Hq) (d : ↥Dw) (y : P),
      LB1EX.ev π (((ihom (Rep.res π ((Rep.resFunctor Dw.subtype).obj P))).obj Aq).ρ τ (psiq Dw πF π σ P A Aq jq ψ d)) y =
        Aq.ρ τ (LB1EX.ev π (psiq Dw πF π σ P A Aq jq ψ d) (P.ρ ((π τ⁻¹ : ↥Dw) : D) y)) := fun _ _ _ => rfl
  have hT' : ∀ (γ : Γ) (d : D) (y : P),
      LB1EX.ev πF (((ihom (Rep.res πF P)).obj A).ρ γ (ψ d)) y = A.ρ γ (LB1EX.ev πF (ψ d) (P.ρ (πF γ⁻¹) y)) :=
    fun _ _ _ => rfl
  rw [d₁₂_hom_apply, d₁₂_hom_apply]
  simp only [Function.comp_apply, LB1EX.ev_add, LB1EX.ev_sub, map_add, map_sub]
  rw [hT, hT', ev_psiq, ev_psiq, ev_psiq, hjq, ← ρ_mul]
  have e1 : ((π τ₂ : ↥Dw) : D) = πF (σ⁻¹ * lg τ₂ * σ) := hπ τ₂
  have e2 : ((π τ₁⁻¹ : ↥Dw) : D) = πF (σ⁻¹ * lg τ₁ * σ)⁻¹ := by
    rw [map_inv, Subgroup.coe_inv, hπ, ← map_inv]
  have e3 : ((π (τ₁ * τ₂) : ↥Dw) : D) = πF (σ⁻¹ * lg τ₁ * σ * (σ⁻¹ * lg τ₂ * σ)) := by
    rw [hπ, map_mul lg]
    congr 1
    group
  have e4 : ((π τ₁ : ↥Dw) : D) = πF (σ⁻¹ * lg τ₁ * σ) := hπ τ₁
  have e5 : lg τ₁ * σ = σ * (σ⁻¹ * lg τ₁ * σ) := by group
  rw [e1, e2, e3, e4, e5, ρ_mul]

theorem κq_eq {p : ℕ} (M : Rep.{0} (ZMod p) Γ) {B : Rep.{0} ℤ D} (g : P ⟶ B)
    (κ : B →+ M →+ A) (κq : B →+ Rep.res lg M →+ Aq)
    (hκq : ∀ (b : B) (mm : M), κq b mm = jq (A.ρ σ (κ b (M.ρ σ⁻¹ mm))))
    (m : Γ × Γ → M)
    (hmrel : ∀ (γ₁ γ₂ : Γ) (y : P), κ (g.hom y) (m (γ₁, γ₂)) =
      LB1EX.ev πF ((d₁₂ ((ihom (Rep.res πF P)).obj A)).hom (ψ ∘ πF) (γ₁, γ₂)) y)
    (hjq : ∀ (τ : Hq) (u : A), Aq.ρ τ (jq u) = jq (A.ρ (lg τ) u))
    (hπ : ∀ τ : Hq, ((π τ : ↥Dw) : D) = πF (σ⁻¹ * lg τ * σ))
    (τ₁ τ₂ : Hq) (y : P) :
    κq (g.hom y) (M.ρ σ (m (σ⁻¹ * lg τ₁ * σ, σ⁻¹ * lg τ₂ * σ))) =
      LB1EX.ev π ((d₁₂ ((ihom (Rep.res π ((Rep.resFunctor Dw.subtype).obj P))).obj Aq)).hom
        ((psiq Dw πF π σ P A Aq jq ψ) ∘ π) (τ₁, τ₂)) y := by
  rw [hκq, LB1EX.ρ_inv_ρ, hmrel, ev_d₁₂_psiq Dw πF lg π σ P A Aq jq ψ hjq hπ]

theorem ρ_ev_psiq_eq (hjq : ∀ (τ : Hq) (u : A), Aq.ρ τ (jq u) = jq (A.ρ (lg τ) u))
    (s : Hq) (hs : ∀ (d : D) (y : P), A.ρ (σ⁻¹ * lg s * σ) (LB1EX.ev πF (ψ d) y) = LB1EX.ev πF (ψ d) y)
    (d : ↥Dw) (y : P) :
    Aq.ρ s (LB1EX.ev π (psiq Dw πF π σ P A Aq jq ψ d) y) = LB1EX.ev π (psiq Dw πF π σ P A Aq jq ψ d) y := by
  rw [ev_psiq, hjq, ← ρ_mul, show lg s * σ = σ * (σ⁻¹ * lg s * σ) by group, ρ_mul, hs]

end generic
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

theorem mem_fixingSubgroup_map_iff (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (σ g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    g ∈ (K.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).fixingSubgroup ↔ σ⁻¹ * g * σ ∈ K.fixingSubgroup := by
  rw [IntermediateField.mem_fixingSubgroup_iff, IntermediateField.mem_fixingSubgroup_iff]
  constructor
  · intro h y hy
    have := h (σ y) ((IntermediateField.mem_map _).2 ⟨y, hy, rfl⟩)
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply]
    change σ⁻¹ (g (σ y)) = y
    rw [this]
    exact σ.symm_apply_apply y
  · intro h y hy
    obtain ⟨z, hz, rfl⟩ := (IntermediateField.mem_map _).1 hy
    have := h z hz
    rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply] at this
    change σ⁻¹ (g (σ z)) = z at this
    calc g (σ z) = σ (σ⁻¹ (g (σ z))) := (σ.apply_symm_apply _).symm
      _ = σ z := by rw [this]

end LB2L
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

namespace LB2L

section concrete

variable {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) [Fact (((q : Nat.Primes) : ℕ)).Prime]
  (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ)))
  (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
  (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F]
  (w : HeightOneSpectrum (𝓞 ↥F))
  (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

noncomputable abbrev jq : Additive (AlgebraicClosure ℚ)ˣ →+ Additive (PadicAlgCl q)ˣ :=
  (Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)).toAdditive

theorem hjq (τ : primeLocalGaloisGroup q) (u : Additive (AlgebraicClosure ℚ)ˣ) :
    (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ τ (jq S q u) =
      jq S q ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ (primeLocalToGlobal q τ) u) := by
  apply Additive.toMul.injective
  change (show PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q from τ) •
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q) (Additive.toMul u) =
    Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q) (primeLocalToGlobal q τ • Additive.toMul u)
  ext
  simp only [AlgEquiv.smul_units_def, Units.coe_map, MonoidHom.coe_coe]
  exact (padicEmbedding_localGaloisToGlobal (q : ℕ) _ _).symm

variable {R P B : Rep ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
  (ψ : (↥F ≃ₐ[ℚ] ↥F) → (ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) P)).obj (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))
  (π : primeLocalGaloisGroup q →* ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w))

noncomputable abbrev ψq : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) →
    (ihom (Rep.res π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).obj P))).obj
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) :=
  psiq (NumberField.PlaceDecomp.decomp ℚ ↥F w) (AlgEquiv.restrictNormalHom ↥F) π σ P
    (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
    (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) (jq S q) ψ

set_option maxHeartbeats 3200000 in

theorem ψq_f
    (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (aw : cocycles₁ ((ihom (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R)).obj
          (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)))
    (haw : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : R),
      Additive.toMul (LinearMap.toAddMonoidHom ((aw : _ → _) d) x) =
        Units.map (algebraMap ↥F (w.adicCompletion ↥F) : ↥F →* w.adicCompletion ↥F)
          (NumberField.SUnits.val ℚ ↥F Sℚ (LinearMap.toAddMonoidHom ((a : _ → _) (d : ↥F ≃ₐ[ℚ] ↥F)) x)))
    (hψ : ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ιE (LinearMap.toAddMonoidHom ((a : _ → _) d) x))
    (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : R) :
    LinearMap.toAddMonoidHom (ψq S q F w σ ψ π d)
        (((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f).hom x) =
      (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (LinearMap.toAddMonoidHom ((aw : _ → _) d) x) := by
  have hev : ∀ z : P, Additive.toMul (LinearMap.toAddMonoidHom (ψq S q F w σ ψ π d) z) =
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
        (σ • Additive.toMul (α := (AlgebraicClosure ℚ)ˣ) (LinearMap.toAddMonoidHom (ψ (d : ↥F ≃ₐ[ℚ] ↥F)) z)) :=
    fun z => rfl
  have hf' : ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f).hom x = f.hom x := rfl
  apply Additive.toMul.injective
  rw [hf', hev, hψ, hιE]
  change _ = Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q) (Additive.toMul (LinearMap.toAddMonoidHom ((aw : _ → _) d) x))
  erw [haw]
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe, AlgEquiv.smul_units_def, hΦF]
  rfl

theorem ψq_level
    (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF₂ : FiniteDimensional ℚ ↥F₂)
    (hfix : ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₂.fixingSubgroup →
      ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : P), (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (LinearMap.toAddMonoidHom (ψ d) x) =
        LinearMap.toAddMonoidHom (ψ d) x) :
    ∃ F' : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F' ∧
      ∀ s : primeLocalGaloisGroup q, primeLocalToGlobal q s ∈ F'.fixingSubgroup →
        ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : (Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).obj P),
          (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)).ρ s
              (LinearMap.toAddMonoidHom (ψq S q F w σ ψ π d) x) =
            LinearMap.toAddMonoidHom (ψq S q F w σ ψ π d) x := by
  haveI := hF₂
  refine ⟨F₂.map (σ : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ), inferInstance, fun s hs d x => ?_⟩
  have hs' := (mem_fixingSubgroup_map_iff F₂ σ (primeLocalToGlobal q s)).1 hs
  exact ρ_ev_psiq_eq (NumberField.PlaceDecomp.decomp ℚ ↥F w) (AlgEquiv.restrictNormalHom ↥F) (primeLocalToGlobal q) π σ P
    (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
    (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) (jq S q) ψ
    (hjq S q) s (fun d' y => hfix _ hs' d' y) d x

set_option maxHeartbeats 3200000 in

theorem local_reading
    (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hπ : ∀ τ : primeLocalGaloisGroup q, ((π τ : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) : ↥F ≃ₐ[ℚ] ↥F) =
      AlgEquiv.restrictNormalHom ↥F (σ⁻¹ * primeLocalToGlobal q τ * σ))
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (κq : B →+ M →+ Additive (PadicAlgCl q)ˣ)
    (hκq : ∀ (b : B) (m : M), Additive.toMul (κq b m) =
      Units.map (padicEmbedding q : AlgebraicClosure ℚ →* PadicAlgCl q)
        (Additive.toMul ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ m)))))
    {Λq : H1 ((ihom (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R)).obj
          (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) →+
        continuousH2 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)}
    (hΛq : IsLocalBridge₂ (primeLocalToGlobal q) π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)
    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (aw : cocycles₁ ((ihom (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R)).obj
          (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)))
    (haw : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : R),
      Additive.toMul (LinearMap.toAddMonoidHom ((aw : _ → _) d) x) =
        Units.map (algebraMap ↥F (w.adicCompletion ↥F) : ↥F →* w.adicCompletion ↥F)
          (NumberField.SUnits.val ℚ ↥F Sℚ (LinearMap.toAddMonoidHom ((a : _ → _) (d : ↥F ≃ₐ[ℚ] ↥F)) x)))

    (hψ : ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ιE (LinearMap.toAddMonoidHom ((a : _ → _) d) x))
    (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ)) (hF₂ : FiniteDimensional ℚ ↥F₂)
    (hfix : ∀ s : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, s ∈ F₂.fixingSubgroup →
      ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : P), (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (LinearMap.toAddMonoidHom (ψ d) x) =
        LinearMap.toAddMonoidHom (ψ d) x)
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M)
    (hmrel : ∀ (γ₁ γ₂ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (x : P), κ (g.hom x) (m (γ₁, γ₂)) =
      LinearMap.toAddMonoidHom ((d₁₂ ((ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) P)).obj
        (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))).hom (ψ ∘ AlgEquiv.restrictNormalHom ↥F) (γ₁, γ₂)) x)
    (hmq : (fun hh : primeLocalGaloisGroup q × primeLocalGaloisGroup q =>
        M.ρ σ (m (σ⁻¹ * primeLocalToGlobal q hh.1 * σ, σ⁻¹ * primeLocalToGlobal q hh.2 * σ))) ∈
      levelCocycles₂ (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)) :
    Λq ((H1π _).hom aw) = continuousH2π (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)
      ⟨fun hh : primeLocalGaloisGroup q × primeLocalGaloisGroup q =>
        M.ρ σ (m (σ⁻¹ * primeLocalToGlobal q hh.1 * σ, σ⁻¹ * primeLocalToGlobal q hh.2 * σ)), hmq⟩ := by
  have hκq' : ∀ (b : B) (mm : M), κq b mm =
      jq S q ((Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ σ (κ b (M.ρ σ⁻¹ mm))) := fun b mm => by
    apply Additive.toMul.injective
    rw [hκq]
    rfl
  exact hΛq aw (ψq S q F w σ ψ π) (ψq_f S q Sℚ F w σ f ψ π Φ hΦF ιE hιE a aw haw hψ)
    (ψq_level S q F w σ ψ π F₂ hF₂ hfix) _
    (fun τ₁ τ₂ y => κq_eq (NumberField.PlaceDecomp.decomp ℚ ↥F w) (AlgEquiv.restrictNormalHom ↥F) (primeLocalToGlobal q) π σ P
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ))
      (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)) (jq S q) ψ
      M g κ κq hκq' m hmrel (hjq S q) hπ τ₁ τ₂ y)
    hmq

end concrete
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

end LB2L
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

namespace LB2EX

variable {k : Type} [CommRing k] {H : Type} [Group H] {D : Type} [Group D] (π : H →* D)
  {R P B : Rep.{0} k D} (f : R ⟶ P) (g : P ⟶ B)
  {X : Rep.{0} k D} {A : Rep.{0} k H} (ι : X →+ A)
  {p : ℕ} {M : Rep.{0} (ZMod p) H} (κ : B →+ M →+ A)

lemma ev_rho (h : H) (c : (ihom (Rep.res π P)).obj A) (x : P) :
    LB1EX.ev π (((ihom (Rep.res π P)).obj A).ρ h c) x = A.ρ h (LB1EX.ev π c (P.ρ (π h⁻¹) x)) := by
  change LinearMap.toAddMonoidHom (((ihom (Rep.res π P)).obj A).ρ h c) x =
    A.ρ h (LinearMap.toAddMonoidHom c ((Rep.res π P).ρ h⁻¹ x))
  erw [Rep.ihom_obj_ρ_apply]
  rfl

noncomputable def cob₂ (ψ : D → (ihom (Rep.res π P)).obj A) (h₁ h₂ : H) : P →+ A :=
  LB1EX.ev π ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom (ψ ∘ π) (h₁, h₂))

lemma cob₂_apply (ψ : D → (ihom (Rep.res π P)).obj A) (h₁ h₂ : H) (x : P) :
    cob₂ π ψ h₁ h₂ x =
      A.ρ h₁ (LB1EX.ev π (ψ (π h₂)) (P.ρ (π h₁⁻¹) x)) - LB1EX.ev π (ψ (π (h₁ * h₂))) x + LB1EX.ev π (ψ (π h₁)) x := by
  change LB1EX.ev π ((d₁₂ ((ihom (Rep.res π P)).obj A)).hom (ψ ∘ π) (h₁, h₂)) x = _
  rw [d₁₂_hom_apply]
  change LB1EX.ev π (((ihom (Rep.res π P)).obj A).ρ h₁ (ψ (π h₂)) - ψ (π (h₁ * h₂)) + ψ (π h₁)) x = _
  rw [LB1EX.ev_add, LB1EX.ev_sub, ev_rho]

section hyps

variable (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
  (hιeq : ∀ (h : H) (x : X), ι (X.ρ (π h) x) = A.ρ h (ι x))
  (hκeq : ∀ (h : H) (b : B) (m : M), κ (B.ρ (π h) b) (M.ρ h m) = A.ρ h (κ b m))
  (hκ : ∀ c : B →+ A, ∃! m : M, ∀ b, κ b m = c b)

include hιeq in

lemma cob₂_apply_f (a : cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψ : ∀ (d : D) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ι (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) d) x))
    (h₁ h₂ : H) (x : R) : cob₂ π ψ h₁ h₂ (f.hom x) = 0 := by
  have hψ' : ∀ (d : D) (y : R), LB1EX.ev π (ψ d) (f.hom y) = ι (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) d) y) := hψ

  have hc := (mem_cocycles₁_iff (a : D → (ihom R).obj X)).1 a.2 (π h₁) (π h₂)
  have hcx : LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) (π h₁ * π h₂)) x =
      X.ρ (π h₁) (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) (π h₂)) (R.ρ (π h₁)⁻¹ x)) +
        LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) (π h₁)) x := by
    have := congrArg (fun c : (ihom R).obj X => LinearMap.toAddMonoidHom c x) hc
    rw [this]
    change LinearMap.toAddMonoidHom (((ihom R).obj X).ρ (π h₁) ((a : D → (ihom R).obj X) (π h₂)) + (a : D → (ihom R).obj X) (π h₁)) x = _
    erw [LinearMap.add_apply, Rep.ihom_obj_ρ_apply]
    rfl
  rw [cob₂_apply, map_inv π h₁, ← Rep.hom_comm_apply, hψ', hψ', hψ', map_mul π, hcx, map_add, hιeq]
  abel

noncomputable def mOf (ψ : D → (ihom (Rep.res π P)).obj A) (h₁ h₂ : H) : M := by
  classical
  exact if hm : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob₂ π ψ h₁ h₂ x then hm.choose else 0

include hfg hg hκ hιeq in
lemma κ_mOf (a : cocycles₁ ((ihom R).obj X)) (ψ : D → (ihom (Rep.res π P)).obj A)
    (hψ : ∀ (d : D) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ι (LinearMap.toAddMonoidHom ((a : D → (ihom R).obj X) d) x))
    (h₁ h₂ : H) (x : P) : κ (g.hom x) (mOf π g κ ψ h₁ h₂) = cob₂ π ψ h₁ h₂ x := by
  classical
  have hex : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob₂ π ψ h₁ h₂ x :=
    LB1EX.exists_forall_κ_eq f g κ hfg hg hκ (cob₂ π ψ h₁ h₂) (cob₂_apply_f π f ι hιeq a ψ hψ h₁ h₂)
  have : mOf π g κ ψ h₁ h₂ = hex.choose := by
    show (if hm : ∃ m : M, ∀ x : P, κ (g.hom x) m = cob₂ π ψ h₁ h₂ x then hm.choose else 0) = _
    rw [dif_pos hex]
  rw [this]
  exact hex.choose_spec x

include hg hκ hκeq in

lemma mem_cocycles₂_of_forall_κ (ψ : D → (ihom (Rep.res π P)).obj A) (n : H × H → M)
    (hn : ∀ (h₁ h₂ : H) (x : P), κ (g.hom x) (n (h₁, h₂)) = cob₂ π ψ h₁ h₂ x) : n ∈ cocycles₂ M := by
  rw [mem_cocycles₂_iff]
  intro h₁ h₂ h₃
  apply LB1EX.κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b

  have hC := (mem_cocycles₂_iff _).1 (d₁₂_apply_mem_cocycles₂ (A := (ihom (Rep.res π P)).obj A) (ψ ∘ π)) h₁ h₂ h₃
  have hCx := congrArg (fun c : (ihom (Rep.res π P)).obj A => LB1EX.ev π c x) hC
  simp only at hCx
  rw [LB1EX.ev_add, LB1EX.ev_add, ev_rho] at hCx
  rw [map_add, map_add, hn, hn, hn, LB1EX.κ_ρ π κ hκeq, ← Rep.hom_comm_apply, hn]
  exact hCx

include hg hκ in

lemma apply_mul_eq_of_forall_κ (ψ : D → (ihom (Rep.res π P)).obj A) (n : H × H → M)
    (hn : ∀ (h₁ h₂ : H) (x : P), κ (g.hom x) (n (h₁, h₂)) = cob₂ π ψ h₁ h₂ x)
    (h₁ h₂ s s' : H) (hs : π s = 1) (hs' : π s' = 1)
    (hfix : ∀ (d : D) (x : P), A.ρ s (LB1EX.ev π (ψ d) x) = LB1EX.ev π (ψ d) x) :
    n (h₁ * s, h₂ * s') = n (h₁, h₂) := by
  apply LB1EX.κ_inj κ hκ
  intro b
  obtain ⟨x, rfl⟩ := hg b
  rw [hn, hn]
  simp only [cob₂_apply, map_mul, map_inv, hs, hs', mul_one, Module.End.mul_apply, hfix]

end hyps
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

end LB2EX
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

namespace LB2G

theorem isUnramifiedOutside_finset_sup (S : Finset Nat.Primes) {ι : Type} (s : Finset ι)
    (F : ι → IntermediateField ℚ (AlgebraicClosure ℚ)) (hF : ∀ i ∈ s, (F i).IsUnramifiedOutside S) :
    (s.sup F).IsUnramifiedOutside S :=
  Finset.sup_induction (p := fun K : IntermediateField ℚ (AlgebraicClosure ℚ) => K.IsUnramifiedOutside S)
    (IntermediateField.isUnramifiedOutside_bot S) (fun _ h₁ _ h₂ => h₁.sup h₂) hF

set_option maxHeartbeats 3200000 in

theorem global_reading
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (hpS : pPrime p ∈ S)
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    {R P B : Rep.{0} ℤ (↥F ≃ₐ[ℚ] ↥F)} (f : R ⟶ P) (g : P ⟶ B)
    (hf : Function.Injective f.hom) (hfg : Function.Exact f.hom g.hom) (hg : Function.Surjective g.hom)
    [Module.Finite ℤ P] (hB : ∀ b : B, p • b = 0)
    (ιE : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hιE : ∀ x, Additive.toMul (ιE x) = Units.map (algebraMap ↥F (AlgebraicClosure ℚ) : ↥F →* AlgebraicClosure ℚ) (NumberField.SUnits.val ℚ ↥F Sℚ x))
    (κ : B →+ M →+ Additive (AlgebraicClosure ℚ)ˣ)
    (hκeq : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (b : B) (m : M),
      κ (B.ρ (AlgEquiv.restrictNormalHom ↥F γ) b) (M.ρ γ m) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (κ b m))
    (hκ : ∀ c : B →+ Additive (AlgebraicClosure ℚ)ˣ, ∃! m : M, ∀ b, κ b m = c b)
    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ))) :
    ∃ (ψ : (↥F ≃ₐ[ℚ] ↥F) → (ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) P)).obj (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))
      (F₂ : IntermediateField ℚ (AlgebraicClosure ℚ))
      (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M),
      (∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : R), LinearMap.toAddMonoidHom (ψ d) (f.hom x) = ιE (LinearMap.toAddMonoidHom ((a : _ → _) d) x)) ∧
      F₂.IsUnramifiedOutside S ∧
      (∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F₂.fixingSubgroup → ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : P),
        (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (LinearMap.toAddMonoidHom (ψ d) x) = LinearMap.toAddMonoidHom (ψ d) x) ∧
      (∀ (γ₁ γ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : P), κ (g.hom x) (m (γ₁, γ₂)) =
        LinearMap.toAddMonoidHom ((d₁₂ ((ihom (Rep.res (AlgEquiv.restrictNormalHom ↥F) P)).obj (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)))).hom (ψ ∘ (AlgEquiv.restrictNormalHom ↥F)) (γ₁, γ₂)) x) ∧
      m ∈ levelCocyclesS₂ S M := by
  classical
  haveI : Fintype (↥F ≃ₐ[ℚ] ↥F) := Fintype.ofFinite _

  have hιeqE : ∀ (γ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ),
      ιE ((NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ).ρ (AlgEquiv.restrictNormalHom ↥F γ) x) = (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ γ (ιE x) := by
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

  have hπF : ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ F.fixingSubgroup → AlgEquiv.restrictNormalHom ↥F s = 1 := by
    intro s hs
    apply AlgEquiv.ext
    intro x
    apply (algebraMap ↥F (AlgebraicClosure ℚ)).injective
    rw [show AlgEquiv.restrictNormalHom ↥F s = s.restrictNormal ↥F from rfl, AlgEquiv.restrictNormal_commutes,
      AlgEquiv.one_apply]
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hs x.1 x.2

  have hlift := NumberField.SUnits.exists_ihom_extension_fixed_of_sLevel_of_injective S hpS Sℚ hSℚ F hF f g hf hfg hg hB ιE hιE
  choose ψ hψ F₂ hF₂ hfix using fun d : ↥F ≃ₐ[ℚ] ↥F => hlift (LinearMap.toAddMonoidHom ((a : _ → _) d))

  have hsup : (Finset.univ.sup F₂).IsUnramifiedOutside S := isUnramifiedOutside_finset_sup S _ F₂ (fun d _ => hF₂ d)
  have hfix' : ∀ s : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ), s ∈ (Finset.univ.sup F₂).fixingSubgroup → ∀ (d : ↥F ≃ₐ[ℚ] ↥F) (x : P),
      (Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)).ρ s (LinearMap.toAddMonoidHom (ψ d) x) = LinearMap.toAddMonoidHom (ψ d) x :=
    fun s hs d x => hfix d s (IntermediateField.fixingSubgroup_antitone (Finset.le_sup (Finset.mem_univ d)) hs) x
  have hm : ∀ (γ₁ γ₂ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (x : P), κ (g.hom x) (LB2EX.mOf (AlgEquiv.restrictNormalHom ↥F) g κ ψ γ₁ γ₂) = LB2EX.cob₂ (AlgEquiv.restrictNormalHom ↥F) ψ γ₁ γ₂ x :=
    LB2EX.κ_mOf (AlgEquiv.restrictNormalHom ↥F) f g ιE κ hfg hg hιeqE hκ a ψ hψ
  refine ⟨ψ, Finset.univ.sup F₂, fun γ => LB2EX.mOf (AlgEquiv.restrictNormalHom ↥F) g κ ψ γ.1 γ.2, hψ, hsup, hfix', fun γ₁ γ₂ x => hm γ₁ γ₂ x, ?_⟩

  rw [mem_levelCocyclesS₂_iff]
  refine ⟨LB2EX.mem_cocycles₂_of_forall_κ (AlgEquiv.restrictNormalHom ↥F) g κ hg hκeq hκ ψ (fun γ => LB2EX.mOf (AlgEquiv.restrictNormalHom ↥F) g κ ψ γ.1 γ.2)
    (fun γ₁ γ₂ x => hm γ₁ γ₂ x), ?_⟩
  refine ⟨F ⊔ Finset.univ.sup F₂, hF.sup hsup, fun γ₁ γ₂ s s' hs hs' => ?_⟩
  exact LB2EX.apply_mul_eq_of_forall_κ (AlgEquiv.restrictNormalHom ↥F) g κ hg hκ ψ (fun γ => LB2EX.mOf (AlgEquiv.restrictNormalHom ↥F) g κ ψ γ.1 γ.2)
    (fun γ₁ γ₂ x => hm γ₁ γ₂ x) γ₁ γ₂ s s'
    (hπF s (IntermediateField.fixingSubgroup_antitone le_sup_left hs))
    (hπF s' (IntermediateField.fixingSubgroup_antitone le_sup_left hs'))
    (fun d x => hfix' s (IntermediateField.fixingSubgroup_antitone le_sup_right hs) d x)

end LB2G
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

namespace LB2A

theorem assemble {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (M : Rep.{0} (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (σ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (m : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) × (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) → M) (hm : m ∈ levelCocyclesS₂ S M)
    (x : continuousH2S S M) (hx : x = continuousH2Sπ S M ⟨m, hm⟩)
    (y : continuousH2 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M))
    (hy : ∀ hmq : (fun hh : primeLocalGaloisGroup q × primeLocalGaloisGroup q =>
        M.ρ σ (m (σ⁻¹ * primeLocalToGlobal q hh.1 * σ, σ⁻¹ * primeLocalToGlobal q hh.2 * σ))) ∈
          levelCocycles₂ (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M),
      y = continuousH2π (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M) ⟨_, hmq⟩) :
    locRes₂S S M (primeLocalToGlobal q) x = y := by
  have hmq : (fun hh : primeLocalGaloisGroup q × primeLocalGaloisGroup q =>
      M.ρ σ (m (σ⁻¹ * primeLocalToGlobal q hh.1 * σ, σ⁻¹ * primeLocalToGlobal q hh.2 * σ))) ∈
        levelCocycles₂ (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M) :=
    EBLB4C.comp_mem_levelCocycles₂_of_mem S M (primeLocalToGlobal q)
      (fun gh => M.ρ σ (m (σ⁻¹ * gh.1 * σ, σ⁻¹ * gh.2 * σ))) (EBLB4C.conj_mem_levelCocyclesS₂ S M σ m hm)
  subst hx
  rw [hy hmq, EBLB4C.locRes₂S_continuousH2Sπ]
  exact (EBLB4C.continuousH2π_conj_eq S M (primeLocalToGlobal q) σ m hm hmq
    (EBLB4C.comp_mem_levelCocycles₂_of_mem S M (primeLocalToGlobal q) m hm)).symm

end LB2A
p2m_reactivate "P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.LB1 P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite.EBLB4C"

theorem solution
    {p : ℕ} [Fact p.Prime] (S : Finset Nat.Primes) (q : ↥S) (hpS : pPrime p ∈ S)
    [Fact (((q : Nat.Primes) : ℕ)).Prime]
    (Sℚ : Finset (HeightOneSpectrum (𝓞 ℚ))) (hSℚ : (↑Sℚ : Set (HeightOneSpectrum (𝓞 ℚ))) = NumberField.placesOverPrimes ℚ (↑S : Set Nat.Primes))
    (M : Rep (ZMod p) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (F : IntermediateField ℚ (AlgebraicClosure ℚ)) [NumberField ↥F] [IsGalois ℚ ↥F] (hF : F.IsUnramifiedOutside S)
    (w : HeightOneSpectrum (𝓞 ↥F))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (Φ : w.adicCompletion ↥F →+* PadicAlgCl q)
    (hΦF : ∀ x : ↥F, Φ (algebraMap ↥F (w.adicCompletion ↥F) x) = padicEmbedding q (σ (x : AlgebraicClosure ℚ)))
    (hcont : Continuous Φ)
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
    {ΛE : H1 ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)) →+ continuousH2S S M}
    (hΛE : IsGlobalBridge₂ S (AlgEquiv.restrictNormalHom ↥F) f g (A := Rep.ofAlgebraAutOnUnits ℚ (AlgebraicClosure ℚ)) ιE κ ΛE)
    {Λq : H1 ((ihom (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R)).obj
          (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)) →+
        continuousH2 (primeLocalToGlobal q) (Rep.res (primeLocalToGlobal q) M)}
    (hΛq : IsLocalBridge₂ (primeLocalToGlobal q) π ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map f)
        ((Rep.resFunctor (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype).map g)
        (X := Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)
        (A := (show Rep ℤ (primeLocalGaloisGroup q) from Rep.ofAlgebraAutOnUnits ℚ_[q] (PadicAlgCl q)))
        (Units.map (Φ : w.adicCompletion ↥F →* PadicAlgCl q)).toAdditive (M := Rep.res (primeLocalToGlobal q) M) κq Λq)
    (a : cocycles₁ ((ihom R).obj (NumberField.SUnits.sUnitsRep ℚ ↥F Sℚ)))
    (aw : cocycles₁ ((ihom (Rep.res (NumberField.PlaceDecomp.decomp ℚ ↥F w).subtype R)).obj
          (Rep.ofMulDistribMulAction ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w) (w.adicCompletion ↥F)ˣ)))
    (haw : ∀ (d : ↥(NumberField.PlaceDecomp.decomp ℚ ↥F w)) (x : R),
      Additive.toMul (LinearMap.toAddMonoidHom ((aw : _ → _) d) x) =
        Units.map (algebraMap ↥F (w.adicCompletion ↥F) : ↥F →* w.adicCompletion ↥F)
          (NumberField.SUnits.val ℚ ↥F Sℚ (LinearMap.toAddMonoidHom ((a : _ → _) (d : ↥F ≃ₐ[ℚ] ↥F)) x))) :
    locRes₂S S M (extArithLoc S (Sum.inr q)) (ΛE ((H1π _).hom a)) = Λq ((H1π _).hom aw) := by

  have H := LB2G.global_reading S hpS Sℚ hSℚ M F hF f g hf hfg hg hB ιE hιE κ hκeq hκ a
  obtain ⟨ψ, F₂, m, Hrest⟩ := H
  obtain ⟨hψ, hF₂S, hfix, hmrel, hm⟩ := Hrest
  have hΛEa := hΛE a ψ hψ ⟨F₂, hF₂S, hfix⟩ m hmrel hm

  exact LB2A.assemble S q M σ m hm _ hΛEa _
    (fun hmq => LB2L.local_reading S q Sℚ M F w σ f g ψ π Φ hΦF hπ ιE hιE κ κq hκq hΛq a aw haw hψ F₂ hF₂S.1 hfix m hmrel hmq)

end S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite
end P2MW
export P2MW.S_NumberField_SUnits_locRes2S_isGlobalBridge2_apply_eq_of_finite (solution)
