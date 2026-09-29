-- Prove2me | solution 1 for NumberField.exists_prime_isArithFrobAt_of_isGalois
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/519fed55-fbc3-5bc0-94c7-527eaa0540c0

import Mathlib
import Theorems.Thm_NumberField_exists_prime_isArithFrobAt_of_isCyclotomicExtension
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois
p2m_attr_erase "instance" "FrobeniusDensity.liesOver_ratBelow FrobeniusDensity.isMaximal_ratPrimeIdeal Deep.NTSupply.instNormalRayClassSubgroup NumberField.NormResidueChar.fintype_G NumberField.NormResidueChar.finite_G"
p2m_attr_erase "simp" "TaylorWiles.Seed.mk.injEq TaylorWiles.Seed.mk.sizeOf_spec"

set_option autoImplicit false
set_option linter.unusedSectionVars false

open scoped Pointwise

noncomputable section

namespace P2mChebotarevCrossing

open NumberField Polynomial

section CosetGenerator

variable {C : Type*} [CommGroup C] [Finite C] [IsCyclic C]

theorem exists_mem_orderOf_mul_eq_card (U : Subgroup C) (a : C)
    (hgen : ∀ x : C, x ∈ Subgroup.zpowers a ⊔ U) :
    ∃ u ∈ U, orderOf (a * u) = Nat.card C := by
  classical
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := C)
  have hm : orderOf g₀ = Nat.card C := orderOf_eq_card_of_forall_mem_zpowers hg₀
  have hmpos : 0 < Nat.card C := Nat.card_pos
  set π : C →* C ⧸ U := QuotientGroup.mk' U with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective U

  have hπa : ∀ y : C ⧸ U, y ∈ Subgroup.zpowers (π a) := by
    intro y
    obtain ⟨x, rfl⟩ := hπsurj y
    obtain ⟨y', hy', z, hz, rfl⟩ := Subgroup.mem_sup.mp (hgen x)
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy'
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hz1 : π z = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    rw [map_mul, map_zpow, hz1, mul_one]
  have hπg₀ : ∀ y : C ⧸ U, y ∈ Subgroup.zpowers (π g₀) := by
    intro y
    obtain ⟨x, rfl⟩ := hπsurj y
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hg₀ x)
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, (map_zpow π g₀ k).symm⟩
  set r : ℕ := Nat.card (C ⧸ U) with hrdef
  have hr : orderOf (π a) = r := orderOf_eq_card_of_forall_mem_zpowers hπa
  have hr' : orderOf (π g₀) = r := orderOf_eq_card_of_forall_mem_zpowers hπg₀
  have hrpos : 0 < r := Nat.card_pos
  have hrm : r ∣ Nat.card C := Subgroup.card_quotient_dvd_card U

  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℕ, (π g₀) ^ k₀ = π a := by
    have h := hπg₀ (π a)
    rw [← mem_powers_iff_mem_zpowers] at h
    exact h
  have hcop : Nat.Coprime k₀ r := by
    have h1 : orderOf ((π g₀) ^ k₀) = r := by rw [hk₀, hr]
    rw [IsOfFinOrder.orderOf_pow _ _ (isOfFinOrder_of_finite _), hr'] at h1

    have hg1 : r.gcd k₀ = 1 := by
      rcases Nat.div_eq_self.mp h1 with h | h
      · exact absurd h hrpos.ne'
      · exact h
    exact Nat.Coprime.symm hg1

  set m : ℕ := Nat.card C with hmdef
  haveI : NeZero m := ⟨hmpos.ne'⟩
  haveI : NeZero r := ⟨hrpos.ne'⟩
  obtain ⟨j, hj⟩ := ZMod.unitsMap_surjective hrm (ZMod.unitOfCoprime k₀ hcop)
  set j₀ : ℕ := (j : ZMod m).val with hj₀def
  have hj₀cop : j₀.Coprime m := ZMod.val_coe_unit_coprime j
  have hj₀mod : j₀ ≡ k₀ [MOD r] := by
    have h1 : ((ZMod.unitsMap hrm j : (ZMod r)ˣ) : ZMod r) = (k₀ : ZMod r) := by
      rw [hj, ZMod.coe_unitOfCoprime]
    rw [ZMod.unitsMap_def, Units.coe_map, MonoidHom.coe_coe, ZMod.castHom_apply,
      ZMod.cast_eq_val] at h1
    exact (ZMod.natCast_eq_natCast_iff j₀ k₀ r).mp h1

  refine ⟨a⁻¹ * g₀ ^ j₀, ?_, ?_⟩
  · rw [← QuotientGroup.eq_one_iff, show (↑(a⁻¹ * g₀ ^ j₀) : C ⧸ U) = π (a⁻¹ * g₀ ^ j₀) from rfl,
      map_mul, map_inv, map_pow, inv_mul_eq_one, ← hk₀]
    exact pow_eq_pow_iff_modEq.mpr (hr'.symm ▸ hj₀mod.symm)
  · rw [mul_inv_cancel_left]
    have hcop' : (orderOf g₀).Coprime j₀ := by rw [hm]; exact hj₀cop.symm
    rw [hcop'.orderOf_pow, hm]

theorem exists_mem_card_dvd_orderOf_mul (U : Subgroup C) (a : C) :
    ∃ u ∈ U, Nat.card U ∣ orderOf (a * u) := by
  set C' : Subgroup C := Subgroup.zpowers a ⊔ U with hC'
  haveI : IsCyclic C' := Subgroup.isCyclic C'
  have haC' : a ∈ C' := Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
  set a' : C' := ⟨a, haC'⟩ with ha'
  set U' : Subgroup C' := U.subgroupOf C' with hU'
  have hgen : ∀ x : C', x ∈ Subgroup.zpowers a' ⊔ U' := by
    rintro ⟨x, hx⟩
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hx
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hzC' : z ∈ C' := Subgroup.mem_sup_right hz
    refine Subgroup.mem_sup.mpr ⟨a' ^ k, Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩, ⟨z, hzC'⟩,
      Subgroup.mem_subgroupOf.mpr hz, ?_⟩
    exact Subtype.ext (by simp [ha'])
  obtain ⟨u', hu', hord⟩ := exists_mem_orderOf_mul_eq_card U' a' hgen
  refine ⟨(u' : C), Subgroup.mem_subgroupOf.mp hu', ?_⟩
  have h1 : orderOf (a * (u' : C)) = Nat.card C' := by
    rw [← hord, ← Subgroup.orderOf_coe]
    rfl
  rw [h1]
  exact Subgroup.card_dvd_of_le le_sup_right

end CosetGenerator

section CycloChar

variable {R L' : Type*} [CommRing R] [Field L'] [Algebra R L'] {q : ℕ} [hq : Fact q.Prime]
  {ζ : L'} (hζ : IsPrimitiveRoot ζ q)

include hζ in
theorem autToPow_eq_one_iff (g : L' ≃ₐ[R] L') : hζ.autToPow R g = 1 ↔ g ζ = ζ := by
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  have hspec := hζ.autToPow_spec R g
  constructor
  · intro h
    rw [← hspec, h, Units.val_one, ZMod.val_one, pow_one]
  · intro h
    have h1 : ζ ^ ((hζ.autToPow R g : (ZMod q)ˣ) : ZMod q).val = ζ ^ 1 := by rw [hspec, h, pow_one]
    have hval : ((hζ.autToPow R g : (ZMod q)ˣ) : ZMod q).val = 1 :=
      hζ.pow_inj (ZMod.val_lt _) hq.out.one_lt h1
    ext
    rw [Units.val_one, ← ZMod.natCast_zmod_val ((hζ.autToPow R g : (ZMod q)ˣ) : ZMod q), hval,
      Nat.cast_one]

end CycloChar

section OverPrime

variable (F : Type*) [Field F]

theorem under_eq_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)} (hQ : Q ≠ ⊤)
    (hqQ : (q : 𝓞 F) ∈ Q) : Q.under ℤ = Ideal.span {(q : ℤ)} := by
  have hmax : (Ideal.span {(q : ℤ)}).IsMaximal :=
    PrincipalIdealRing.isMaximal_of_irreducible
      (Int.prime_iff_natAbs_prime.mpr (by simpa using hq)).irreducible
  have h1 : Ideal.span {(q : ℤ)} ≤ Q.under ℤ := by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.under, Ideal.mem_comap,
      map_natCast]
    exact hqQ
  have h2 : Q.under ℤ ≠ ⊤ := Ideal.comap_ne_top _ hQ
  exact (hmax.eq_of_le h2 h1).symm

theorem card_quotient_under_of_natCast_mem {q : ℕ} (hq : q.Prime) {Q : Ideal (𝓞 F)}
    (hQ : Q ≠ ⊤) (hqQ : (q : 𝓞 F) ∈ Q) : Nat.card (ℤ ⧸ Q.under ℤ) = q := by
  rw [under_eq_of_natCast_mem F hq hQ hqQ,
    Nat.card_congr (Int.quotientSpanNatEquivZMod q).toEquiv, Nat.card_zmod]

end OverPrime

section Crossing

variable (K L L' : Type) [Field K] [NumberField K] [Field L] [NumberField L]
  [Field L'] [NumberField L'] [Algebra K L] [Algebra L L'] [Algebra K L'] [IsScalarTower K L L']
  [IsGalois K L] [IsGalois K L'] (q : ℕ) [hq : Fact q.Prime] [IsCyclotomicExtension {q} L L']

def liftL (g : L' ≃ₐ[K] L') (hg : ∀ x : L, g (algebraMap L L' x) = algebraMap L L' x) :
    L' ≃ₐ[L] L' :=
  { g.toRingEquiv with commutes' := hg }

@[scoped simp]
theorem liftL_apply (g : L' ≃ₐ[K] L') (hg : ∀ x : L, g (algebraMap L L' x) = algebraMap L L' x)
    (y : L') : liftL K L L' g hg y = g y := rfl

theorem apply_algebraMap_of_mem_ker {g : L' ≃ₐ[K] L'}
    (hg : g ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).ker) (x : L) :
    g (algebraMap L L' x) = algebraMap L L' x := by
  rw [MonoidHom.mem_ker] at hg
  have h := AlgEquiv.restrictNormal_commutes g L x
  have h' : AlgEquiv.restrictNormalHom L g = g.restrictNormal L := rfl
  rw [← h', hg, AlgEquiv.one_apply] at h
  exact h.symm

theorem restrictScalars_mem_ker (gL : L' ≃ₐ[L] L') :
    gL.restrictScalars K ∈ (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).ker := by
  rw [MonoidHom.mem_ker]
  ext x
  apply (algebraMap L L').injective
  have h' : AlgEquiv.restrictNormalHom L (gL.restrictScalars K) =
      (gL.restrictScalars K).restrictNormal L := rfl
  rw [h', AlgEquiv.restrictNormal_commutes, AlgEquiv.one_apply, AlgEquiv.restrictScalars_apply,
    AlgEquiv.commutes]

def kerEquiv :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := L') L).ker ≃ (L' ≃ₐ[L] L') where
  toFun g := liftL K L L' g.1 (apply_algebraMap_of_mem_ker K L L' g.2)
  invFun gL := ⟨gL.restrictScalars K, restrictScalars_mem_ker K L L' gL⟩
  left_inv g := by ext; rfl
  right_inv gL := by ext; rfl

theorem crossing (L' : Type) [Field L'] [NumberField L'] [Algebra L L'] [Algebra K L']
    [IsScalarTower K L L'] [IsGalois K L'] [IsCyclotomicExtension {q} L L'] (σ : L ≃ₐ[K] L)
    (hqmod : orderOf σ * (Module.finrank ℚ L).factorial ∣ q - 1) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ σ P := by
  classical
  haveI : NeZero q := ⟨hq.out.ne_zero⟩
  haveI hGalL : IsGalois L L' := IsCyclotomicExtension.isGalois {q} L L'
  set n : ℕ := orderOf σ with hndef
  set D : ℕ := Module.finrank ℚ L with hDdef
  have hnpos : 0 < n := orderOf_pos σ
  have hDpos : 0 < D := Module.finrank_pos

  set ζ : L' := IsCyclotomicExtension.zeta q L L' with hζdef
  have hζ : IsPrimitiveRoot ζ q := IsCyclotomicExtension.zeta_spec q L L'
  set χ : (L' ≃ₐ[K] L') →* (ZMod q)ˣ := hζ.autToPow K with hχdef
  set χL : (L' ≃ₐ[L] L') →* (ZMod q)ˣ := hζ.autToPow L with hχLdef
  have hχL_inj : Function.Injective χL := hζ.autToPow_injective L

  set res : (L' ≃ₐ[K] L') →* (L ≃ₐ[K] L) := AlgEquiv.restrictNormalHom L with hresdef
  set N : Subgroup (L' ≃ₐ[K] L') := res.ker with hNdef

  have hF1 : ∀ g ∈ N, χ g = 1 → g = 1 := by
    intro g hg hχg
    have hgζ : g ζ = ζ := (autToPow_eq_one_iff hζ g).mp hχg
    set gL := liftL K L L' g (apply_algebraMap_of_mem_ker K L L' hg) with hgL
    have hgLζ : gL ζ = ζ := hgζ
    have hχLg : χL gL = 1 := (autToPow_eq_one_iff hζ gL).mpr hgLζ
    have hgL1 : gL = 1 := hχL_inj (by rw [hχLg, map_one])
    ext y
    have := congrArg (fun e : L' ≃ₐ[L] L' => e y) hgL1
    simpa [hgL] using this

  have hcardN : Nat.card N = Module.finrank L L' := by
    rw [Nat.card_congr (kerEquiv K L L'), IsGalois.card_aut_eq_finrank]
  have he1 : Module.finrank L L' ∣ q - 1 := by
    have h1 : Nat.card (L' ≃ₐ[L] L') ∣ Nat.card (ZMod q)ˣ :=
      Subgroup.card_dvd_of_injective χL hχL_inj
    rwa [IsGalois.card_aut_eq_finrank, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient,
      Nat.totient_prime hq.out] at h1
  have he2 : q - 1 ≤ Module.finrank L L' * D := by
    have h1 : (minpoly ℚ ζ).natDegree ≤ Module.finrank ℚ L' := minpoly.natDegree_le ζ
    rw [← cyclotomic_eq_minpoly_rat hζ hq.out.pos, natDegree_cyclotomic,
      Nat.totient_prime hq.out] at h1
    rw [hDdef, mul_comm, Module.finrank_mul_finrank ℚ L L']
    exact h1
  have hne : n ∣ Module.finrank L L' := by
    set e := Module.finrank L L' with hedef
    obtain ⟨d, hd⟩ := he1
    have hq1 : 0 < q - 1 := by have := hq.out.two_le; omega
    have hdpos : 0 < d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · rw [h, mul_zero] at hd; omega
      · exact h
    have hepos : 0 < e := by
      rcases Nat.eq_zero_or_pos e with h | h
      · rw [h, zero_mul] at hd; omega
      · exact h
    have hdD : d ≤ D := by
      have : e * d ≤ e * D := by rw [← hd]; exact he2
      exact Nat.le_of_mul_le_mul_left this hepos
    obtain ⟨c, hc⟩ := Nat.dvd_factorial hdpos hdD
    have h2 : n * c * d ∣ e * d := by
      have : n * D.factorial = n * c * d := by rw [hc]; ring
      rw [← this, ← hd]; exact hqmod
    have h3 : n * c ∣ e := Nat.dvd_of_mul_dvd_mul_right hdpos h2
    exact (Dvd.intro c rfl).trans h3
  have hnN : n ∣ Nat.card N := hcardN ▸ hne

  obtain ⟨σ₁, hσ₁⟩ := AlgEquiv.restrictNormalHom_surjective L' σ
  set ψ : N →* (ZMod q)ˣ := χ.comp N.subtype with hψdef
  have hψ_inj : Function.Injective ψ := by
    intro g h hgh
    have h1 : ψ (g * h⁻¹) = 1 := by rw [map_mul, map_inv, hgh, mul_inv_cancel]
    have h2 : (g * h⁻¹ : N).1 = 1 := hF1 _ (g * h⁻¹).2 h1
    have h3 : g * h⁻¹ = 1 := Subtype.ext h2
    exact mul_inv_eq_one.mp h3
  have hcardψ : Nat.card ψ.range = Nat.card N :=
    (Nat.card_congr (MonoidHom.ofInjective hψ_inj).toEquiv).symm
  obtain ⟨u, hu, hdiv⟩ := exists_mem_card_dvd_orderOf_mul ψ.range (χ σ₁)
  obtain ⟨⟨h, hhN⟩, rfl⟩ := MonoidHom.mem_range.mp hu
  set σ' : L' ≃ₐ[K] L' := σ₁ * h with hσ'def
  have hσ'res : res σ' = σ := by
    rw [hσ'def, map_mul, (MonoidHom.mem_ker).mp hhN, mul_one]
    exact hσ₁
  have hnord : n ∣ orderOf (χ σ') := by
    have h1 : χ σ' = χ σ₁ * ψ ⟨h, hhN⟩ := by rw [hσ'def, map_mul]; rfl
    rw [h1]
    exact (hcardψ ▸ hnN).trans hdiv

  have hkey : ∀ k : ℕ, (σ' ^ k) ζ = ζ → σ' ^ k = 1 := by
    intro k hk
    have h1 : χ (σ' ^ k) = 1 := (autToPow_eq_one_iff hζ _).mpr hk
    have h2 : n ∣ k := by
      rw [map_pow] at h1
      exact hnord.trans (orderOf_dvd_of_pow_eq_one h1)
    have h3 : σ ^ k = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one]; exact h2
    have h4 : σ' ^ k ∈ N := by
      rw [MonoidHom.mem_ker, map_pow, hσ'res, h3]
    exact hF1 _ h4 h1

  set Hσ : Subgroup (L' ≃ₐ[K] L') := Subgroup.zpowers σ' with hHσdef
  set M : IntermediateField K L' := IntermediateField.fixedField Hσ with hMdef
  let eM : Hσ ≃* (L' ≃ₐ[M] L') := IntermediateField.subgroupEquivAlgEquiv Hσ
  set τ : L' ≃ₐ[M] L' := eM ⟨σ', Subgroup.mem_zpowers σ'⟩ with hτdef
  have hτ_apply : ∀ y : L', τ y = σ' y := fun y => rfl
  have heM_apply : ∀ (w : Hσ) (y : L'), eM w y = (w : L' ≃ₐ[K] L') y := fun w y => rfl
  haveI hcycM : IsCyclotomicExtension {q} M L' := by
    have htop : IntermediateField.adjoin M {ζ} = ⊤ := by
      have hfix : (IntermediateField.adjoin M {ζ}).fixingSubgroup = ⊥ := by
        rw [eq_bot_iff]
        intro g hg
        rw [IntermediateField.mem_fixingSubgroup_iff] at hg
        have hgζ : g ζ = ζ := hg ζ (IntermediateField.mem_adjoin_simple_self M ζ)
        obtain ⟨w, rfl⟩ := eM.surjective g
        obtain ⟨k, hk⟩ : ∃ k : ℕ, σ' ^ k = (w : L' ≃ₐ[K] L') := by
          have hw := w.2
          rw [← mem_powers_iff_mem_zpowers] at hw
          exact hw
        have hk1 : σ' ^ k = 1 := hkey k (by rw [hk, ← heM_apply]; exact hgζ)
        have hw1 : w = 1 := Subtype.ext (hk.symm.trans hk1)
        rw [hw1, map_one]
        exact Subgroup.mem_bot.mpr rfl
      calc IntermediateField.adjoin M {ζ}
          = IntermediateField.fixedField (IntermediateField.adjoin M {ζ}).fixingSubgroup :=
            (IsGalois.fixedField_fixingSubgroup _).symm
        _ = ⊤ := by rw [hfix, IntermediateField.fixedField_bot]
    have halg : Algebra.adjoin M {ζ} = ⊤ := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        (Algebra.IsAlgebraic.isAlgebraic ζ), htop, IntermediateField.top_toSubalgebra]
    refine ⟨fun {k} hk _ => ?_, fun x => ?_⟩
    · rw [Set.mem_singleton_iff] at hk
      subst hk
      exact ⟨ζ, hζ⟩
    · have hx : x ∈ Algebra.adjoin M {ζ} := halg ▸ Algebra.mem_top
      refine Algebra.adjoin_mono ?_ hx
      rw [Set.singleton_subset_iff]
      exact ⟨q, Set.mem_singleton q, NeZero.ne q, hζ.pow_eq_one⟩

  obtain ⟨p, hp, hpS, P', hP'max, hpP', hfrob'⟩ :=
    NumberField.exists_prime_isArithFrobAt_of_isCyclotomicExtension M L' q τ S
  set P : Ideal (𝓞 L) := P'.comap (algebraMap (𝓞 L) (𝓞 L')) with hPdef
  have hpP : (p : 𝓞 L) ∈ P := by
    rw [hPdef, Ideal.mem_comap, map_natCast]
    exact hpP'
  haveI : P'.IsPrime := hP'max.isPrime
  haveI hPprime : P.IsPrime := Ideal.comap_isPrime _ P'
  have hPne : P ≠ ⊥ := by
    intro hbot
    have hp0 : (p : 𝓞 L) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    exact hp0 (by simpa [hbot] using hpP)
  have hPmax : P.IsMaximal := hPprime.isMaximal hPne
  refine ⟨p, hp, hpS, P, hPmax, hpP, ?_⟩

  have hcP : Nat.card (ℤ ⧸ P.under ℤ) = p :=
    card_quotient_under_of_natCast_mem L hp hPmax.ne_top hpP
  have hcP' : Nat.card (ℤ ⧸ P'.under ℤ) = p :=
    card_quotient_under_of_natCast_mem L' hp hP'max.ne_top hpP'
  have hcoe : ∀ y : 𝓞 L, ((algebraMap (𝓞 L) (𝓞 L') y : 𝓞 L') : L') = algebraMap L L' (y : L) := by
    intro y
    rw [show ((algebraMap (𝓞 L) (𝓞 L') y : 𝓞 L') : L') =
        algebraMap (𝓞 L') L' (algebraMap (𝓞 L) (𝓞 L') y) from rfl,
      ← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply (𝓞 L) L L']
  have hστ : ∀ x : 𝓞 L, algebraMap (𝓞 L) (𝓞 L') (MulSemiringAction.toAlgHom ℤ (𝓞 L) σ x) =
      MulSemiringAction.toAlgHom ℤ (𝓞 L') τ (algebraMap (𝓞 L) (𝓞 L') x) := by
    intro x
    apply RingOfIntegers.ext
    rw [MulSemiringAction.toAlgHom_apply, MulSemiringAction.toAlgHom_apply, hcoe]
    change algebraMap L L' (σ (x : L)) = τ ((algebraMap (𝓞 L) (𝓞 L') x : 𝓞 L') : L')
    rw [hτ_apply, hcoe, ← hσ'res]
    exact AlgEquiv.restrictNormal_commutes σ' L (x : L)
  intro x
  rw [hcP, hPdef, Ideal.mem_comap, map_sub, map_pow, hστ]
  have hx := hfrob' (algebraMap (𝓞 L) (𝓞 L') x)
  rw [hcP'] at hx
  exact hx

end Crossing

section Assembly

variable (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

theorem isGalois_cyclotomicField (q : ℕ) [NeZero q] : IsGalois K (CyclotomicField q L) := by
  obtain ⟨f, -, hf⟩ := IsGalois.is_separable_splitting_field K L
  have key : ∀ g : K[X], g ≠ 0 → IsSplittingField K L g → Normal K (CyclotomicField q L) := by
    intro g hg hgs
    haveI := hgs
    haveI : IsSplittingField L (CyclotomicField q L) ((cyclotomic q K).map (algebraMap K L)) := by
      rw [map_cyclotomic]
      exact IsCyclotomicExtension.splitting_field_cyclotomic q L (CyclotomicField q L)
    haveI : IsSplittingField K (CyclotomicField q L) (g * cyclotomic q K) :=
      IsSplittingField.mul (F := K) (K := L) (CyclotomicField q L) g (cyclotomic q K) hg
        (cyclotomic_ne_zero q K)
    exact Normal.of_isSplittingField (g * cyclotomic q K)
  haveI : Normal K (CyclotomicField q L) := by
    by_cases hf0 : f = 0
    · subst hf0
      refine key 1 one_ne_zero ⟨?_, ?_⟩
      · rw [Polynomial.map_one]; exact Polynomial.Splits.one
      · rw [rootSet_one]
        have h := IsSplittingField.adjoin_rootSet L (0 : K[X])
        rwa [rootSet_zero] at h
    · exact key f hf0 hf
  haveI : FiniteDimensional K (CyclotomicField q L) := Module.Finite.trans L (CyclotomicField q L)
  haveI : Algebra.IsSeparable K (CyclotomicField q L) :=
    Algebra.IsAlgebraic.isSeparable_of_perfectField
  exact ⟨⟩

theorem main (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ σ P := by
  set n : ℕ := orderOf σ with hn
  set D : ℕ := Module.finrank ℚ L with hD
  have hnpos : 0 < n := orderOf_pos σ
  have hk : n * D.factorial ≠ 0 := mul_ne_zero hnpos.ne' (Nat.factorial_ne_zero D)
  obtain ⟨q, hqprime, -, hqmod⟩ := Nat.exists_prime_gt_modEq_one 2 hk
  haveI : Fact q.Prime := ⟨hqprime⟩
  haveI : NeZero q := ⟨hqprime.ne_zero⟩
  haveI : IsGalois K (CyclotomicField q L) := isGalois_cyclotomicField K L q
  have hdvd : n * D.factorial ∣ q - 1 := (Nat.modEq_iff_dvd' hqprime.one_le).mp hqmod.symm
  exact crossing K L q (CyclotomicField q L) σ hdvd S

end Assembly

end P2mChebotarevCrossing
p2m_reactivate "P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois.P2mChebotarevCrossing"

end
p2m_reactivate "P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois.P2mChebotarevCrossing"

open NumberField in
theorem solution (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [IsGalois K L] (σ : L ≃ₐ[K] L) (S : Finset ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ∉ S ∧ ∃ P : Ideal (𝓞 L), P.IsMaximal ∧ (p : 𝓞 L) ∈ P ∧
      IsArithFrobAt ℤ σ P :=
  P2mChebotarevCrossing.main K L σ S

end S_NumberField_exists_prime_isArithFrobAt_of_isGalois
end P2MW
export P2MW.S_NumberField_exists_prime_isArithFrobAt_of_isGalois (solution)
