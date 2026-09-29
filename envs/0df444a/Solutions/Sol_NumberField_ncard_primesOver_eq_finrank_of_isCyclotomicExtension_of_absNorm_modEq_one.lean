-- Prove2me | solution 1 for NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/2d2d169c-f5bb-5e25-bcaf-d646f763b7a0

import Mathlib
import Definitions.Def_LanglandsTunnell_NormClass
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one

set_option autoImplicit false

namespace P2mCycloSplit

open NumberField Polynomial IsDedekindDomain

set_option linter.unusedSectionVars false

variable {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

theorem algEquiv_eq_of_apply_eq (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L] {ζ : L}
    (hζ : IsPrimitiveRoot ζ m) {σ τ : L ≃ₐ[K] L} (h : σ ζ = τ ζ) : σ = τ := by
  apply hζ.autToPow_injective K
  have hσ := hζ.autToPow_spec K σ
  have hτ := hζ.autToPow_spec K τ
  have hpow : ζ ^ ((hζ.autToPow K σ : ZMod m)).val = ζ ^ ((hζ.autToPow K τ : ZMod m)).val := by
    rw [hσ, hτ, h]
  have hval := hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hpow
  exact Units.ext (ZMod.val_injective m hval)

theorem card_le_of_forall_pow_eq {F : Type*} [Field F] [Fintype F] {q : ℕ} (hq : 1 < q)
    (h : ∀ y : F, y ^ q = y) : Fintype.card F ≤ q := by
  classical
  set P : F[X] := X ^ q - X with hP
  have hP0 : P ≠ 0 := FiniteField.X_pow_card_sub_X_ne_zero F hq
  have hdeg : P.natDegree = q := FiniteField.X_pow_card_sub_X_natDegree_eq F hq
  have hsub : (Finset.univ : Finset F).val ≤ P.roots := by
    rw [Multiset.le_iff_subset (Finset.univ : Finset F).nodup]
    intro y _
    rw [mem_roots hP0, IsRoot, hP, eval_sub, eval_pow, eval_X, h y, sub_self]
  calc Fintype.card F = Multiset.card (Finset.univ : Finset F).val := rfl
    _ ≤ Multiset.card P.roots := Multiset.card_le_card hsub
    _ ≤ P.natDegree := card_roots' P
    _ = q := hdeg

theorem eq_of_pow_eq_one_of_sub_mem (m : ℕ) [NeZero m] {w : Ideal (𝓞 L)} (hN1 : Ideal.absNorm w ≠ 1)
    (hNcop : (Ideal.absNorm w).Coprime m) {x y : 𝓞 L} (hx : x ^ m = 1) (hy : y ^ m = 1)
    (hxy : x - y ∈ w) : x = y := by
  have hinj := Ideal.rootsOfUnityMapQuot_injective (I := w) m hN1 hNcop
  set x' : rootsOfUnity m (𝓞 L) := rootsOfUnity.mkOfPowEq x hx with hx'
  set y' : rootsOfUnity m (𝓞 L) := rootsOfUnity.mkOfPowEq y hy with hy'
  have hval : ((x' : (𝓞 L)ˣ) : 𝓞 L) = x := rfl
  have hval' : ((y' : (𝓞 L)ˣ) : 𝓞 L) = y := rfl
  have heq : Ideal.rootsOfUnityMapQuot w m x' = Ideal.rootsOfUnityMapQuot w m y' := by
    apply Units.ext
    have h1 : ((Ideal.rootsOfUnityMapQuot w m x' : (𝓞 L ⧸ w)ˣ) : 𝓞 L ⧸ w) =
        Ideal.Quotient.mk w x := by
      rw [show x' = ⟨(x' : (𝓞 L)ˣ), x'.2⟩ from rfl, Ideal.rootsOfUnityMapQuot_apply, hval]
    have h2 : ((Ideal.rootsOfUnityMapQuot w m y' : (𝓞 L ⧸ w)ˣ) : 𝓞 L ⧸ w) =
        Ideal.Quotient.mk w y := by
      rw [show y' = ⟨(y' : (𝓞 L)ˣ), y'.2⟩ from rfl, Ideal.rootsOfUnityMapQuot_apply, hval']
    rw [h1, h2, Ideal.Quotient.eq]
    exact hxy
  have := hinj heq
  rw [← hval, ← hval', this]

theorem main (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (v : Ideal (𝓞 K)) [hvmax : v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
    (h1 : (Ideal.absNorm v : ZMod m) = 1) :
    (v.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
      ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) → Ideal.absNorm w = Ideal.absNorm v := by
  classical
  haveI : IsGalois K L := IsCyclotomicExtension.isGalois {m} K L
  haveI : IsGaloisGroup (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing (L ≃ₐ[K] L) (𝓞 K) (𝓞 L) K L
  obtain ⟨ζ, hζ⟩ := IsCyclotomicExtension.exists_isPrimitiveRoot K L (Set.mem_singleton m)
    (NeZero.ne m)
  set ζ' : 𝓞 L := hζ.toInteger with hζ'def
  have hζ' : IsPrimitiveRoot ζ' m := hζ.toInteger_isPrimitiveRoot
  set q : ℕ := Ideal.absNorm v with hqdef

  have hvbot : v ≠ ⊥ := (v.bot_lt_of_maximal (RingOfIntegers.not_isField K)).ne'
  have hq1 : q ≠ 1 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_one_iff]
    exact hvmax.ne_top
  have hq0 : q ≠ 0 := by
    rw [hqdef, Ne, Ideal.absNorm_eq_zero_iff]
    exact hvbot
  have hq2 : 1 < q := by omega
  have hcardv : Nat.card (𝓞 K ⧸ v) = q := by
    rw [hqdef, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hqv : (q : 𝓞 K) ∈ v := by rw [hqdef]; exact Ideal.absNorm_mem v

  have hmv : (m : 𝓞 K) ∉ v := by
    intro hm
    apply hvmax.ne_top
    rw [Ideal.eq_top_iff_one]
    have hg := Nat.gcd_eq_gcd_ab q m
    rw [Nat.Coprime.gcd_eq_one hcop] at hg
    have h1' : (1 : 𝓞 K) = (q : 𝓞 K) * (Nat.gcdA q m : 𝓞 K) + (m : 𝓞 K) * (Nat.gcdB q m : 𝓞 K) := by
      have := congrArg (fun z : ℤ => (z : 𝓞 K)) hg
      push_cast at this
      exact this
    rw [h1']
    exact v.add_mem (v.mul_mem_right _ hqv) (v.mul_mem_right _ hm)

  have hζ'q : ζ' ^ q = ζ' := by
    have hmod : q % m = 1 % m := (ZMod.natCast_eq_natCast_iff' q 1 m).mp (by rw [Nat.cast_one]; exact h1)
    rw [← pow_mod_orderOf ζ' q, ← hζ'.eq_orderOf, hmod, hζ'.eq_orderOf, pow_mod_orderOf, pow_one]

  have hw_facts : ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) →
      w.IsMaximal ∧ (m : 𝓞 L) ∉ w ∧ Ideal.absNorm w ≠ 1 ∧ (Ideal.absNorm w).Coprime m := by
    intro w hw
    obtain ⟨hwp, hwo⟩ := hw
    have hwbot : w ≠ ⊥ := Ideal.ne_bot_of_liesOver_of_ne_bot hvbot w
    have hwmax : w.IsMaximal := hwp.isMaximal hwbot
    have hmw : (m : 𝓞 L) ∉ w := by
      intro hm
      apply hmv
      have : algebraMap (𝓞 K) (𝓞 L) (m : 𝓞 K) ∈ w := by rwa [map_natCast]
      rw [← Ideal.mem_comap] at this
      have hunder : w.under (𝓞 K) = v := (hwo.over).symm
      rw [← hunder]
      exact this
    have hN1 : Ideal.absNorm w ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      exact hwmax.ne_top
    have hNcop : (Ideal.absNorm w).Coprime m := by
      have h := LanglandsTunnell.P2.Artin.absNorm_coprime_of_not_dvd L m ⟨w, hwp, hwbot⟩ (by
        intro hdvd
        apply hmw
        have hle : Ideal.span {(m : 𝓞 L)} ≤ w := Ideal.le_of_dvd hdvd
        exact hle (Ideal.mem_span_singleton_self _))
      exact h
    exact ⟨hwmax, hmw, hN1, hNcop⟩

  have hkey : ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) →
      Nat.card (Ideal.inertia (L ≃ₐ[K] L) w) = 1 ∧ Nat.card (𝓞 L ⧸ w) = q := by
    intro w hw
    obtain ⟨hwmax, hmw, hN1, hNcop⟩ := hw_facts w hw
    haveI : w.IsMaximal := hwmax
    haveI : w.LiesOver v := hw.2
    have hunder : w.under (𝓞 K) = v := (hw.2.over).symm
    constructor
    ·
      rw [Nat.card_eq_one_iff_unique]
      refine ⟨⟨fun a b => ?_⟩, ⟨1⟩⟩
      have hmem : ∀ σ : Ideal.inertia (L ≃ₐ[K] L) w, (σ : L ≃ₐ[K] L) = 1 := by
        intro σ
        have hσ : ∀ x : 𝓞 L, (σ : L ≃ₐ[K] L) • x - x ∈ w := AddSubgroup.mem_inertia.mp σ.2
        have hfix : (σ : L ≃ₐ[K] L) • ζ' = ζ' := by
          apply eq_of_pow_eq_one_of_sub_mem m hN1 hNcop _ hζ'.pow_eq_one (hσ ζ')
          rw [← smul_pow', hζ'.pow_eq_one, smul_one]
        have hfixL : (σ : L ≃ₐ[K] L) ζ = ζ := by
          have h := congrArg (fun x : 𝓞 L => (x : L)) hfix
          simp [hζ'def, hζ.coe_toInteger] at h
          exact h
        exact algEquiv_eq_of_apply_eq m hζ (by rw [hfixL, AlgEquiv.one_apply])
      exact Subtype.ext ((hmem a).trans (hmem b).symm)
    ·
      set φ : L ≃ₐ[K] L := arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w with hφdef
      have hφ : IsArithFrobAt (𝓞 K) φ w := IsArithFrobAt.arithFrobAt (𝓞 K) (L ≃ₐ[K] L) w
      have hcardK : Nat.card (𝓞 K ⧸ w.under (𝓞 K)) = q := by rw [hunder, hcardv]
      have hφζ' : φ • ζ' = ζ' := by
        have h := AlgHom.IsArithFrobAt.apply_of_pow_eq_one hφ hζ'.pow_eq_one hmw
        rw [hcardK, hζ'q] at h
        exact h
      have hφζ : φ ζ = ζ := by
        have h := congrArg (fun x : 𝓞 L => (x : L)) hφζ'
        simp [hζ'def, hζ.coe_toInteger] at h
        exact h
      have hφ1 : φ = 1 := algEquiv_eq_of_apply_eq m hζ (by rw [hφζ, AlgEquiv.one_apply])
      have hpow : ∀ y : 𝓞 L ⧸ w, y ^ q = y := by
        intro y
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        have hx := hφ x
        rw [hcardK, hφ1] at hx
        have hx' : x - x ^ q ∈ w := by
          have h1x : (MulSemiringAction.toAlgHom (𝓞 K) (𝓞 L) (1 : L ≃ₐ[K] L)) x = x := one_smul _ x
          rwa [h1x] at hx
        rw [← map_pow, eq_comm, Ideal.Quotient.eq]
        exact hx'
      letI : Field (𝓞 L ⧸ w) := Ideal.Quotient.field w
      letI : Fintype (𝓞 L ⧸ w) := Fintype.ofFinite _
      have hle : Fintype.card (𝓞 L ⧸ w) ≤ q := card_le_of_forall_pow_eq hq2 hpow

      letI : Field (𝓞 K ⧸ v) := Ideal.Quotient.field v
      have hpowf : Nat.card (𝓞 L ⧸ w) = q ^ Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ w) := by
        rw [Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ v), hcardv]
      have hfpos : 0 < Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ w) := Module.finrank_pos
      have hcardw : Nat.card (𝓞 L ⧸ w) = Fintype.card (𝓞 L ⧸ w) := Nat.card_eq_fintype_card
      have hf1 : Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ w) = 1 := by
        by_contra hf
        have hf2 : 2 ≤ Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ w) := by omega
        have : q ^ 2 ≤ q := by
          calc q ^ 2 ≤ q ^ Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ w) :=
                Nat.pow_le_pow_right (by omega) hf2
            _ = Fintype.card (𝓞 L ⧸ w) := by rw [← hpowf, hcardw]
            _ ≤ q := hle
        nlinarith
      rw [hpowf, hf1, pow_one]
  constructor
  ·
    obtain ⟨w₀, hw₀⟩ := (v.nonempty_primesOver (S := 𝓞 L))
    have hw₀' : (w₀ : Ideal (𝓞 L)) ∈ v.primesOver (𝓞 L) := hw₀
    obtain ⟨hwmax, hmw, hN1, hNcop⟩ := hw_facts w₀ hw₀'
    haveI : (w₀ : Ideal (𝓞 L)).IsMaximal := hwmax
    haveI : (w₀ : Ideal (𝓞 L)).LiesOver v := hw₀'.2
    letI : Field (𝓞 L ⧸ (w₀ : Ideal (𝓞 L))) := Ideal.Quotient.field _
    letI : Field (𝓞 K ⧸ v) := Ideal.Quotient.field v
    have hid := Ideal.ncard_primesOver_mul_card_inertia_mul_finrank (G := L ≃ₐ[K] L) v (w₀ : Ideal (𝓞 L))
    obtain ⟨hin, hcw⟩ := hkey w₀ hw₀'
    have hf1 : Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ (w₀ : Ideal (𝓞 L))) = 1 := by
      have hpowf : Nat.card (𝓞 L ⧸ (w₀ : Ideal (𝓞 L))) =
          q ^ Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ (w₀ : Ideal (𝓞 L))) := by
        rw [Module.natCard_eq_pow_finrank (K := 𝓞 K ⧸ v), hcardv]
      rw [hcw] at hpowf
      have h' : q ^ 1 = q ^ Module.finrank (𝓞 K ⧸ v) (𝓞 L ⧸ (w₀ : Ideal (𝓞 L))) := by
        rw [pow_one]; exact hpowf
      exact (Nat.pow_right_injective hq2 h').symm
    rw [hin, ← Ideal.inertiaDeg'_eq_inertiaDeg v (w₀ : Ideal (𝓞 L)), Ideal.inertiaDeg'_algebraMap, hf1,
      mul_one, mul_one, IsGalois.card_aut_eq_finrank] at hid
    exact hid
  · intro w hw
    obtain ⟨-, hcw⟩ := hkey w hw
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply, hcw]

end P2mCycloSplit

open NumberField in
theorem solution
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (v : Ideal (𝓞 K)) [v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
    (h1 : (Ideal.absNorm v : ZMod m) = 1) :
    (v.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
      ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) → Ideal.absNorm w = Ideal.absNorm v :=
  P2mCycloSplit.main m v hcop h1

end S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
end P2MW
export P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one (solution)
