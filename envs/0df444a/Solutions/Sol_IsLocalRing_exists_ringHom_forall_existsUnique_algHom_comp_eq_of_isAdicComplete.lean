-- Prove2me | solution 1 for IsLocalRing.exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/68cf736d-0426-54d8-a63c-3a566436d9b6

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace R4Yoneda

open IsLocalRing

variable {O : Type} [CommRing O] [IsLocalRing O]
variable {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]

abbrev Q (R : Type) [CommRing R] [IsLocalRing R] (n : ℕ) : Type := R ⧸ maximalIdeal R ^ (n + 1)

theorem pow_ne_top (n : ℕ) : maximalIdeal R ^ (n + 1) ≠ ⊤ :=
  fun h => (maximalIdeal.isMaximal R).ne_top (by
    rw [eq_top_iff, ← h]
    exact Ideal.pow_le_self (Nat.succ_ne_zero n))

scoped instance nontrivial_Q (n : ℕ) : Nontrivial (Q R n) :=
  Ideal.Quotient.nontrivial_iff.mpr (pow_ne_top n)

scoped instance isLocalRing_Q (n : ℕ) : IsLocalRing (Q R n) :=
  IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective

theorem maximalIdeal_Q_le (n : ℕ) :
    maximalIdeal (Q R n) ≤ (maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) := by
  intro x hx
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  have hr : r ∈ maximalIdeal R := by
    rw [mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (mem_maximalIdeal _ |>.mp hx) (hu.map _)
  exact Ideal.mem_map_of_mem _ hr

scoped instance isArtinianRing_Q (n : ℕ) : IsArtinianRing (Q R n) := by
  rw [isArtinianRing_iff_isNilpotent_maximalIdeal]
  refine ⟨n + 1, ?_⟩
  show maximalIdeal (Q R n) ^ (n + 1) = ⊥
  rw [← le_bot_iff]
  calc maximalIdeal (Q R n) ^ (n + 1)
      ≤ ((maximalIdeal R).map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))) ^ (n + 1) :=
        Ideal.pow_right_mono (maximalIdeal_Q_le n) _
    _ = (maximalIdeal R ^ (n + 1)).map (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) := by
        rw [Ideal.map_pow]
    _ = ⊥ := Ideal.map_quotient_self _
    _ ≤ ⊥ := le_rfl

section Res

variable (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)

include hresR in
theorem resR_surjective : Function.Surjective resR := by
  intro c
  obtain ⟨o, rfl⟩ := IsLocalRing.residue_surjective c
  exact ⟨algebraMap O R o, by rw [← RingHom.comp_apply, hresR]⟩

include hresR in
theorem ker_resR : RingHom.ker resR = maximalIdeal R :=
  IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resR (resR_surjective resR hresR))

include hresR in
theorem pow_le_ker (n : ℕ) : ∀ a ∈ maximalIdeal R ^ (n + 1), resR a = 0 := by
  intro a ha
  have : a ∈ maximalIdeal R := Ideal.pow_le_self (Nat.succ_ne_zero n) ha
  rw [← ker_resR resR hresR] at this
  exact this

noncomputable def resQ (n : ℕ) : Q R n →+* ResidueField O :=
  Ideal.Quotient.lift _ resR (pow_le_ker resR hresR n)

theorem resQ_mk (n : ℕ) (r : R) : resQ resR hresR n (Ideal.Quotient.mk _ r) = resR r :=
  Ideal.Quotient.lift_mk _ _ _

theorem resQ_surjective (n : ℕ) : Function.Surjective (resQ resR hresR n) := by
  intro c
  obtain ⟨r, rfl⟩ := resR_surjective resR hresR c
  exact ⟨Ideal.Quotient.mk _ r, resQ_mk resR hresR n r⟩

theorem resQ_comp_algebraMap (n : ℕ) : (resQ resR hresR n).comp (algebraMap O (Q R n)) = residue O := by
  ext o
  show resQ resR hresR n (Ideal.Quotient.mk _ (algebraMap O R o)) = residue O o
  rw [resQ_mk, ← RingHom.comp_apply, hresR]

noncomputable def proj (O : Type) [CommRing O] {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R] (n : ℕ) :
    R →ₐ[O] Q R n := Ideal.Quotient.mkₐ O _

theorem resQ_comp_proj (n : ℕ) : (resQ resR hresR n).comp (proj O n : R →ₐ[O] Q R n).toRingHom = resR := by
  ext r
  exact resQ_mk resR hresR n r

noncomputable def trans (O : Type) [CommRing O] {R : Type} [CommRing R] [IsLocalRing R] [Algebra O R]
    {m n : ℕ} (h : m ≤ n) : Q R n →ₐ[O] Q R m :=
  Ideal.Quotient.factorₐ O (Ideal.pow_le_pow_right (Nat.succ_le_succ h))

theorem trans_comp_proj {m n : ℕ} (h : m ≤ n) : (trans O h).comp (proj O n) = (proj O m : R →ₐ[O] Q R m) :=
  Ideal.Quotient.factorₐ_comp_mk O _

theorem resQ_comp_trans {m n : ℕ} (h : m ≤ n) :
    (resQ resR hresR m).comp (trans O h : Q R n →ₐ[O] Q R m).toRingHom = resQ resR hresR n := by
  apply Ideal.Quotient.ringHom_ext
  ext r
  show resQ resR hresR m (trans O h (Ideal.Quotient.mk _ r)) = resQ resR hresR n (Ideal.Quotient.mk _ r)
  rw [trans, Ideal.Quotient.factorₐ_apply_mk, resQ_mk, resQ_mk]

end Res

theorem main
    (S : Type) [CommRing S] (xbar : S →+* ResidueField O)
    [IsAdicComplete (maximalIdeal R) R]
    (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)
    (β : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar → (R →ₐ[O] A))
    (hβ_res : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        resA.comp (β A resA hs hc ψ hψ).toRingHom = resR)
    (hβ_inj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (ψ₁ : S →+* A) (hψ₁ : resA.comp ψ₁ = xbar) (ψ₂ : S →+* A) (hψ₂ : resA.comp ψ₂ = xbar),
        β A resA hs hc ψ₁ hψ₁ = β A resA hs hc ψ₂ hψ₂ → ψ₁ = ψ₂)
    (hβ_surj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (χ : R →ₐ[O] A),
        resA.comp χ.toRingHom = resR → ∃ (ψ : S →+* A) (hψ : resA.comp ψ = xbar), β A resA hs hc ψ hψ = χ)
    (hβ_nat : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (A' : Type) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
        (hc' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA →
        ∀ (ψ : S →+* A) (hψ : resA.comp ψ = xbar) (hψ' : resA'.comp (f.toRingHom.comp ψ) = xbar),
        β A' resA' hs' hc' (f.toRingHom.comp ψ) hψ' = f.comp (β A resA hs hc ψ hψ)) :
    ∃ φ : S →+* R, resR.comp φ = xbar ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O), Function.Surjective resA →
          resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar →
          ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ) ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        (β A resA hs hc ψ hψ).toRingHom.comp φ = ψ) := by

  have hsurjQ := fun n => resQ_surjective resR hresR n
  have hcQ := fun n => resQ_comp_algebraMap resR hresR n
  have hπ := fun n => resQ_comp_proj resR hresR n
  choose φQ hφQ hβφQ using fun n =>
    hβ_surj (Q R n) (resQ resR hresR n) (hsurjQ n) (hcQ n) (proj O n) (hπ n)

  have hcompat : ∀ {m n : ℕ} (h : m ≤ n), (trans O h : Q R n →ₐ[O] Q R m).toRingHom.comp (φQ n) = φQ m := by
    intro m n h
    apply hβ_inj (Q R m) (resQ resR hresR m) (hsurjQ m) (hcQ m) _ ?_ _ (hφQ m)
    · rw [hβ_nat (Q R n) (resQ resR hresR n) (hsurjQ n) (hcQ n) (Q R m) (resQ resR hresR m) (hsurjQ m) (hcQ m)
        (trans O h) (resQ_comp_trans resR hresR h) (φQ n) (hφQ n), hβφQ n, hβφQ m, trans_comp_proj]
    · rw [← RingHom.comp_assoc, resQ_comp_trans, hφQ]

  have ha : StrictMono (fun n : ℕ => n + 1) := fun a b h => Nat.succ_lt_succ h
  have hcompat' : ∀ {m : ℕ},
      (Ideal.Quotient.factorPow (maximalIdeal R) (ha.monotone m.le_succ)).comp (φQ (m + 1)) = φQ m :=
    fun {m} => hcompat m.le_succ
  let φ : S →+* R := IsAdicComplete.StrictMono.liftRingHom (maximalIdeal R) ha φQ hcompat'
  have hφproj : ∀ n, (proj O n : R →ₐ[O] Q R n).toRingHom.comp φ = φQ n := fun n =>
    IsAdicComplete.StrictMono.mk_comp_liftRingHom (maximalIdeal R) ha φQ hcompat'

  have key : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
      (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
      (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
      (β A resA hs hc ψ hψ).toRingHom.comp φ = ψ := by
    intro A _ _ _ _ resA hs hc ψ hψ
    set χ := β A resA hs hc ψ hψ with hχdef
    have hχres : resA.comp χ.toRingHom = resR := hβ_res A resA hs hc ψ hψ

    have hkerA : RingHom.ker resA = maximalIdeal A :=
      IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective resA hs)
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := A)
    have hmA : maximalIdeal A ^ N = ⊥ := by
      rw [← IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
      exact hN
    have hχm : ∀ r ∈ maximalIdeal R, χ r ∈ maximalIdeal A := by
      intro r hr
      rw [← hkerA, RingHom.mem_ker]
      have := congrArg (fun g : R →+* ResidueField O => g r) hχres
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom] at this
      rw [this, ← RingHom.mem_ker, ker_resR resR hresR]
      exact hr
    have hχpow : ∀ r ∈ maximalIdeal R ^ (N + 1), χ r = 0 := by
      intro r hr
      have h1 : χ r ∈ (maximalIdeal R ^ (N + 1)).map χ.toRingHom := Ideal.mem_map_of_mem _ hr
      rw [Ideal.map_pow] at h1
      have h2 : (maximalIdeal R).map χ.toRingHom ≤ maximalIdeal A := by
        rw [Ideal.map_le_iff_le_comap]
        intro r hr
        exact hχm r hr
      have h3 := Ideal.pow_le_pow_right (Nat.le_succ N) (Ideal.pow_right_mono h2 (N + 1) h1)
      rw [hmA] at h3
      exact h3

    let χbar : Q R N →ₐ[O] A := Ideal.Quotient.liftₐ _ χ hχpow
    have hχbar : χbar.comp (proj O N) = χ := Ideal.Quotient.liftₐ_comp _ χ hχpow
    have hχbar_res : resA.comp χbar.toRingHom = resQ resR hresR N := by
      apply Ideal.Quotient.ringHom_ext
      ext r
      show resA (χbar (proj O N r)) = resQ resR hresR N (Ideal.Quotient.mk _ r)
      rw [← AlgHom.comp_apply, hχbar, resQ_mk]
      exact congrArg (fun g : R →+* ResidueField O => g r) hχres

    have hψ' : resA.comp (χbar.toRingHom.comp (φQ N)) = xbar := by
      rw [← RingHom.comp_assoc, hχbar_res, hφQ]
    have hnat := hβ_nat (Q R N) (resQ resR hresR N) (hsurjQ N) (hcQ N) A resA hs hc χbar hχbar_res
      (φQ N) (hφQ N) hψ'
    rw [hβφQ, hχbar] at hnat
    have heq : χbar.toRingHom.comp (φQ N) = ψ := hβ_inj A resA hs hc _ hψ' _ hψ hnat
    calc χ.toRingHom.comp φ = (χbar.comp (proj O N)).toRingHom.comp φ := by rw [hχbar]
      _ = χbar.toRingHom.comp ((proj O N : R →ₐ[O] Q R N).toRingHom.comp φ) := rfl
      _ = χbar.toRingHom.comp (φQ N) := by rw [hφproj]
      _ = ψ := heq
  refine ⟨φ, ?_, ?_, key⟩
  ·
    have h0 : resR = (resQ resR hresR 0).comp (proj O 0 : R →ₐ[O] Q R 0).toRingHom := (hπ 0).symm
    rw [h0, RingHom.comp_assoc, hφproj, hφQ]
  · intro A _ _ _ _ resA hs hc ψ hψ
    refine ⟨β A resA hs hc ψ hψ, ⟨hβ_res A resA hs hc ψ hψ, key A resA hs hc ψ hψ⟩, ?_⟩
    rintro χ' ⟨hχ'res, hχ'φ⟩
    obtain ⟨ψ', hψ', hβψ'⟩ := hβ_surj A resA hs hc χ' hχ'res
    have hk := key A resA hs hc ψ' hψ'
    rw [hβψ', hχ'φ] at hk
    subst hk
    exact hβψ'.symm

end R4Yoneda
p2m_reactivate "P2MW.S_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete.R4Yoneda"

open IsLocalRing in
theorem solution
    (O : Type) [CommRing O] [IsLocalRing O]
    (S : Type) [CommRing S] (xbar : S →+* ResidueField O)
    (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [Algebra O R]
    [IsAdicComplete (maximalIdeal R) R]
    (resR : R →+* ResidueField O) (hresR : resR.comp (algebraMap O R) = residue O)
    (β : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O), Function.Surjective resA →
        resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar → (R →ₐ[O] A))
    (hβ_res : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        resA.comp (β A resA hs hc ψ hψ).toRingHom = resR)
    (hβ_inj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (ψ₁ : S →+* A) (hψ₁ : resA.comp ψ₁ = xbar) (ψ₂ : S →+* A) (hψ₂ : resA.comp ψ₂ = xbar),
        β A resA hs hc ψ₁ hψ₁ = β A resA hs hc ψ₂ hψ₂ → ψ₁ = ψ₂)
    (hβ_surj : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O) (χ : R →ₐ[O] A),
        resA.comp χ.toRingHom = resR → ∃ (ψ : S →+* A) (hψ : resA.comp ψ = xbar), β A resA hs hc ψ hψ = χ)
    (hβ_nat : ∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
        (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
        (hc : resA.comp (algebraMap O A) = residue O)
        (A' : Type) [CommRing A'] [IsLocalRing A'] [IsArtinianRing A'] [Algebra O A']
        (resA' : A' →+* ResidueField O) (hs' : Function.Surjective resA')
        (hc' : resA'.comp (algebraMap O A') = residue O)
        (f : A →ₐ[O] A'), resA'.comp f.toRingHom = resA →
        ∀ (ψ : S →+* A) (hψ : resA.comp ψ = xbar) (hψ' : resA'.comp (f.toRingHom.comp ψ) = xbar),
        β A' resA' hs' hc' (f.toRingHom.comp ψ) hψ' = f.comp (β A resA hs hc ψ hψ)) :
    ∃ φ : S →+* R, resR.comp φ = xbar ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O), Function.Surjective resA →
          resA.comp (algebraMap O A) = residue O →
        ∀ ψ : S →+* A, resA.comp ψ = xbar →
          ∃! χ : R →ₐ[O] A, resA.comp χ.toRingHom = resR ∧ χ.toRingHom.comp φ = ψ) ∧
      (∀ (A : Type) [CommRing A] [IsLocalRing A] [IsArtinianRing A] [Algebra O A]
          (resA : A →+* ResidueField O) (hs : Function.Surjective resA)
          (hc : resA.comp (algebraMap O A) = residue O) (ψ : S →+* A) (hψ : resA.comp ψ = xbar),
        (β A resA hs hc ψ hψ).toRingHom.comp φ = ψ) :=
  R4Yoneda.main S xbar resR hresR β hβ_res hβ_inj hβ_surj hβ_nat

end S_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete
end P2MW
export P2MW.S_IsLocalRing_exists_ringHom_forall_existsUnique_algHom_comp_eq_of_isAdicComplete (solution)
