-- Prove2me | solution 1 for HeckeEis.exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/426fabaf-3ff0-5be5-9873-b91e3fb7d743

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq
import Theorems.Thm_ModularCurve_index_heckeUpper
import Theorems.Thm_HeckeEis_exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd

set_option autoImplicit false

namespace QuadTwist3

open CongruenceSubgroup HeckeEis
open scoped MatrixGroups

section Induced

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N ℓ : ℕ) [NeZero ℓ] (ρ : Representation K (Gamma0 N) V) (a : V →ₗ[K] V)

def IsCompat : Prop :=
  ∀ u : ↥(heckeUpper N ℓ), a ∘ₗ ρ (heckeConj N ℓ u) = ρ (u : Gamma0 N) ∘ₗ a

noncomputable def heckeLin : (Gamma0 N → V) →ₗ[K] (Gamma0 N → V) where
  toFun := coeffHeckeFun N ℓ ρ a
  map_add' z w := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c z := by
    letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
    ext g
    simp only [coeffHeckeFun_apply, Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

@[scoped simp] theorem heckeLin_apply (z : Gamma0 N → V) : heckeLin N ℓ ρ a z = coeffHeckeFun N ℓ ρ a z := rfl

variable {N ℓ ρ a}

noncomputable def heckeZ1 (ha : IsCompat N ℓ ρ a) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) :=
  (heckeLin N ℓ ρ a).restrict fun _ hz => coeffHeckeFun_mem_coeffCocycles N ℓ ρ a ha hz

@[scoped simp] theorem coe_heckeZ1 (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    (heckeZ1 ha z : Gamma0 N → V) = coeffHeckeFun N ℓ ρ a z := rfl

noncomputable def heckeH1 (ha : IsCompat N ℓ ρ a) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (heckeZ1 ha)
    fun _ hz => coeffHeckeFun_mem_coeffCoboundaries N ℓ ρ a ha hz

theorem heckeH1_mk (ha : IsCompat N ℓ ρ a) (z : ↥(coeffCocycles ρ)) :
    heckeH1 ha (coeffH1Mk ρ z) = coeffH1Mk ρ (heckeZ1 ha z) := rfl

theorem isCoeffHeckeOnH1_heckeH1 (ha : IsCompat N ℓ ρ a) : IsCoeffHeckeOnH1 N ℓ ρ a (heckeH1 ha) :=
  fun z => ⟨heckeZ1 ha z, rfl, rfl⟩

theorem unique_of_isCoeffHeckeOnH1 {T T' : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T)
    (hT' : IsCoeffHeckeOnH1 N ℓ ρ a T') : T = T' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  obtain ⟨w, hw, hTw⟩ := hT z
  obtain ⟨w', hw', hTw'⟩ := hT' z
  rw [hTw, hTw']
  congr 1
  exact Subtype.ext (hw.trans hw'.symm)

theorem eq_heckeH1_of_isCoeffHeckeOnH1 (ha : IsCompat N ℓ ρ a) {T : coeffH1 ρ →ₗ[K] coeffH1 ρ}
    (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) : T = heckeH1 ha :=
  unique_of_isCoeffHeckeOnH1 hT (isCoeffHeckeOnH1_heckeH1 ha)

theorem coeffH1Mk_eq_iff (z w : ↥(coeffCocycles ρ)) :
    coeffH1Mk ρ z = coeffH1Mk ρ w ↔ (z : Gamma0 N → V) - w ∈ coeffCoboundaries ρ :=
  (Submodule.Quotient.eq _).trans Submodule.mem_comap

end Induced

section Comm

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {N : ℕ} {ρ : Representation K (Gamma0 N) V}

theorem heckeH1_comm {ℓ ℓ' : ℕ} [NeZero ℓ] [NeZero ℓ'] (hℓ : ℓ.Prime) (hℓ' : ℓ'.Prime)
    (hℓN : ¬ ℓ ∣ N) (hℓ'N : ¬ ℓ' ∣ N) (hne : ℓ ≠ ℓ') {a a' : V →ₗ[K] V}
    (ha : IsCompat N ℓ ρ a) (ha' : IsCompat N ℓ' ρ a') (hcomm : a ∘ₗ a' = a' ∘ₗ a) (x : coeffH1 ρ) :
    heckeH1 ha (heckeH1 ha' x) = heckeH1 ha' (heckeH1 ha x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [heckeH1_mk, heckeH1_mk, heckeH1_mk, heckeH1_mk, coeffH1Mk_eq_iff]
  simp only [coe_heckeZ1]
  haveI : NeZero (ℓ * ℓ') := ⟨mul_ne_zero (NeZero.ne ℓ) (NeZero.ne ℓ')⟩
  have hℓℓ' : ¬ ℓ ∣ ℓ' := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ hℓ').mp h)
  have hℓ'ℓ : ¬ ℓ' ∣ ℓ := fun h => hne ((Nat.prime_dvd_prime_iff_eq hℓ' hℓ).mp h).symm
  have h1 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ ℓ' (ℓ * ℓ')
    hℓ hℓN hℓℓ' rfl ρ a a' ha ha' z.2
  have h2 := coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries N ℓ' ℓ (ℓ * ℓ')
    hℓ' hℓ'N hℓ'ℓ (Nat.mul_comm ℓ ℓ') ρ a' a ha' ha z.2
  rw [← hcomm] at h2
  have h3 := (coeffCoboundaries ρ).sub_mem h1 h2
  convert h3 using 1
  abel

end Comm

section FiniteDim

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem cocycle_apply_eq_zero_of_closure {G : Type*} [Group G] (ρ : Representation K G V)
    (z : ↥(coeffCocycles ρ)) (S : Set G) (hS : ∀ s ∈ S, (z : G → V) s = 0)
    (g : G) (hg : g ∈ Subgroup.closure S) : (z : G → V) g = 0 := by
  have hz := z.2
  induction hg using Subgroup.closure_induction with
  | mem x hx => exact hS x hx
  | one =>
    have h := hz 1 1
    rw [mul_one, map_one, Module.End.one_apply] at h

    have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel this
  | mul x y _ _ ihx ihy => rw [hz x y, ihx, ihy, map_zero, zero_add]
  | inv x _ ih =>
    have h := hz x x⁻¹
    have h1 : (z : G → V) 1 = 0 := by
      have h' := hz 1 1
      rw [mul_one, map_one, Module.End.one_apply] at h'
      have : (z : G → V) 1 + (z : G → V) 1 = (z : G → V) 1 + 0 := by rw [add_zero]; exact h'.symm
      exact add_left_cancel this
    rw [mul_inv_cancel, h1, ih, zero_add] at h

    have h2 : ρ x⁻¹ (ρ x ((z : G → V) x⁻¹)) = 0 := by rw [← h, map_zero]
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2

theorem finiteDimensional_coeffH1 (N : ℕ) [NeZero N] [FiniteDimensional K V]
    (ρ : Representation K (Gamma0 N) V) : FiniteDimensional K (coeffH1 ρ) := by

  haveI hSL : Group.FG SL(2, ℤ) :=
    Group.fg_iff.mpr ⟨{ModularGroup.S, ModularGroup.T}, SpecialLinearGroup.SL2Z_generators,
      Set.toFinite _⟩
  have hΓ : Group.FG (Gamma0 N) := inferInstance
  obtain ⟨S, hS⟩ := hΓ.out

  let ev : ↥(coeffCocycles ρ) →ₗ[K] (↥S → V) :=
    { toFun := fun z s => (z : Gamma0 N → V) s
      map_add' := fun z w => by ext s; rfl
      map_smul' := fun c z => by ext s; rfl }
  have hev : Function.Injective ev := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    refine Subtype.ext (funext fun g => ?_)
    have hg : g ∈ Subgroup.closure (S : Set (Gamma0 N)) := by rw [hS]; trivial
    exact cocycle_apply_eq_zero_of_closure ρ z S (fun s hs => congrFun hz ⟨s, hs⟩) g hg
  haveI : FiniteDimensional K ↥(coeffCocycles ρ) := Module.Finite.of_injective ev hev
  exact Module.Finite.of_surjective (coeffH1Mk ρ) (coeffH1Mk_surjective ρ)

end FiniteDim

section LinAlg

variable {F : Type*} [Field F]

theorem coe_restrict_pow {M : Type*} [AddCommGroup M] [Module F M] (f : M →ₗ[F] M)
    (P : Submodule F M) (h : ∀ v ∈ P, f v ∈ P) (k : ℕ) (v : ↥P) :
    (((f.restrict h) ^ k) v : M) = (f ^ k) (v : M) := by
  induction k generalizing v with
  | zero => rfl
  | succ k ih => rw [pow_succ, pow_succ, Module.End.mul_apply, Module.End.mul_apply, ih]; rfl

theorem exists_common_ker_of_nilpotent : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → (∀ i, IsNilpotent (T i)) → Nontrivial M →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT hnil hM hd
  by_cases hz : ∀ i, T i = 0
  · obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact ⟨v, hv, fun i => by rw [hz i, LinearMap.zero_apply]⟩
  push Not at hz
  obtain ⟨i₀, hi₀⟩ := hz
  set P : Submodule F M := LinearMap.ker (T i₀) with hP
  have hPtop : P ≠ ⊤ := fun h => hi₀ (LinearMap.ker_eq_top.mp h)
  have hPbot : P ≠ ⊥ := by
    intro h
    have hinj : Function.Injective (T i₀) := LinearMap.ker_eq_bot.mp h
    obtain ⟨k, hk⟩ := hnil i₀
    have hinjk : Function.Injective ((T i₀) ^ k) := by
      rw [Module.End.coe_pow]; exact Function.Injective.iterate hinj k
    obtain ⟨v, hv⟩ := exists_ne (0 : M)
    exact hv (hinjk (by rw [hk, map_zero, LinearMap.zero_apply]))
  have hstab : ∀ i, ∀ v ∈ P, T i v ∈ P := by
    intro i v hv
    rw [hP, LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, (hT i₀ i).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P →ₗ[F] ↥P := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hnil' : ∀ i, IsNilpotent (T' i) := by
    intro i
    obtain ⟨k, hk⟩ := hnil i
    refine ⟨k, LinearMap.ext fun v => Subtype.ext ?_⟩
    change ((((T i).restrict (hstab i)) ^ k) v : M) = ((0 : ↥P →ₗ[F] ↥P) v : M)
    rw [coe_restrict_pow, hk]
    rfl
  haveI : Nontrivial ↥P := Submodule.nontrivial_iff_ne_bot.mpr hPbot
  have hlt : Module.finrank F ↥P < d := hd ▸ Submodule.finrank_lt hPtop
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' hnil' inferInstance rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_ker_of_range_le : ∀ (d : ℕ) {M : Type*} [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] {ι : Type*} (T : ι → M →ₗ[F] M),
    (∀ i j, Commute (T i) (T j)) → ∀ (P : Submodule F M), P ≠ ⊤ → (∀ i x, T i x ∈ P) →
    Module.finrank F M = d → ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = 0 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro M _ _ _ ι T hT P hP hTP hd
  by_cases hall : ∀ i, IsNilpotent (T i)
  ·
    have hex : ∃ v : M, v ∉ P := by
      by_contra h
      push Not at h
      exact hP (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hv⟩ := hex
    have hv0 : v ≠ 0 := fun h => hv (h ▸ P.zero_mem)
    haveI : Nontrivial M := nontrivial_of_ne v 0 hv0
    exact exists_common_ker_of_nilpotent d T hT hall inferInstance hd
  push Not at hall
  obtain ⟨i₀, hi₀⟩ := hall
  set f := T i₀ with hf

  obtain ⟨k, hk, hk1⟩ :=
    ((LinearMap.eventually_isCompl_ker_pow_range_pow f).and (Filter.eventually_ge_atTop 1)).exists
  set P' : Submodule F M := LinearMap.ker (f ^ k) with hP'
  set Q : Submodule F M := LinearMap.range (f ^ k) with hQ
  have hQbot : Q ≠ ⊥ := by
    intro h
    apply hi₀
    exact ⟨k, LinearMap.range_eq_bot.mp h⟩
  have hP'top : P' ≠ ⊤ := by
    intro h
    have hdis := hk.disjoint
    rw [h] at hdis
    exact hQbot (top_disjoint.mp hdis)

  have hQP : Q ≤ P := by
    rintro _ ⟨x, rfl⟩
    have hfk : f ^ k = f * f ^ (k - 1) := by rw [← pow_succ', Nat.sub_add_cancel hk1]
    rw [hfk, Module.End.mul_apply]
    exact hTP i₀ _

  have hP'P : P.comap P'.subtype ≠ ⊤ := by
    intro h
    have hle : P' ≤ P := fun v hv => by
      have : (⟨v, hv⟩ : ↥P') ∈ P.comap P'.subtype := by rw [h]; trivial
      exact this
    apply hP
    rw [eq_top_iff, ← hk.codisjoint.eq_top]
    exact sup_le hle hQP

  have hstab : ∀ i, ∀ v ∈ P', T i v ∈ P' := by
    intro i v hv
    rw [hP', LinearMap.mem_ker] at hv ⊢
    rw [← Module.End.mul_apply, ((hT i₀ i).pow_left k).eq, Module.End.mul_apply, hv, map_zero]
  let T' : ι → ↥P' →ₗ[F] ↥P' := fun i => (T i).restrict (hstab i)
  have hT' : ∀ i j, Commute (T' i) (T' j) := fun i j =>
    LinearMap.ext fun v => Subtype.ext (LinearMap.congr_fun (hT i j).eq (v : M))
  have hTP' : ∀ i (x : ↥P'), T' i x ∈ P.comap P'.subtype := fun i x => hTP i (x : M)
  have hlt : Module.finrank F ↥P' < d := hd ▸ Submodule.finrank_lt hP'top
  obtain ⟨v, hv, hTv⟩ := ih _ hlt T' hT' (P.comap P'.subtype) hP'P hTP' rfl
  refine ⟨(v : M), fun h => hv (Subtype.ext h), fun i => ?_⟩
  exact congrArg Subtype.val (hTv i)

theorem exists_common_eigenvector {M : Type*} [AddCommGroup M] [Module F M] [FiniteDimensional F M]
    {ι : Type*} (T : ι → M →ₗ[F] M) (hT : ∀ i j, Commute (T i) (T j)) (c : ι → F)
    (P : Submodule F M) (hP : P ≠ ⊤) (hTP : ∀ i x, T i x - c i • x ∈ P) :
    ∃ v : M, v ≠ 0 ∧ ∀ i, T i v = c i • v := by
  let T' : ι → M →ₗ[F] M := fun i => T i - c i • 1
  have hT' : ∀ i j, Commute (T' i) (T' j) := by
    intro i j
    refine Commute.sub_left (Commute.sub_right (hT i j) ?_) (Commute.sub_right ?_ ?_)
    · exact (Commute.one_right _).smul_right _
    · exact (Commute.one_left _).smul_left _
    · exact ((Commute.refl (1 : M →ₗ[F] M)).smul_right _).smul_left _
  have hTP' : ∀ i x, T' i x ∈ P := fun i x => by
    simpa [T', LinearMap.sub_apply, LinearMap.smul_apply] using hTP i x
  obtain ⟨v, hv, hTv⟩ := exists_common_ker_of_range_le _ T' hT' P hP hTP' rfl
  refine ⟨v, hv, fun i => ?_⟩
  have := hTv i
  simp only [T', LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at this
  exact this

end LinAlg

section Systems

def Good (N : ℕ) (S₀ : Set ℕ) (ℓ : ℕ) : Prop := ℓ.Prime ∧ ¬ ℓ ∣ N ∧ ℓ ∉ S₀

theorem Good.neZero {N : ℕ} {S₀ : Set ℕ} {ℓ : ℕ} (h : Good N S₀ ℓ) : NeZero ℓ := ⟨h.1.ne_zero⟩

variable {K : Type*} [Field K] {N : ℕ} (S₀ : Set ℕ)
variable {V : Type*} [AddCommGroup V] [Module K V]

def GoodCompat (ρ : Representation K (Gamma0 N) V) (a : ℕ → (V →ₗ[K] V)) : Prop :=
  ∀ (ℓ : ℕ) (h : Good N S₀ ℓ), @IsCompat K _ V _ _ N ℓ h.neZero ρ (a ℓ)

noncomputable def Tgood {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (ℓ : ℕ) (h : Good N S₀ ℓ) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  @heckeH1 K _ V _ _ N ℓ h.neZero ρ (a ℓ) (hc ℓ h)

def IsEigvec {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (lam : ℕ → K) (x : coeffH1 ρ) : Prop :=
  ∀ (ℓ : ℕ) (h : Good N S₀ ℓ), Tgood S₀ hc ℓ h x = lam ℓ • x

def GoodCommute {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) : Prop :=
  ∀ (ℓ ℓ' : ℕ) (h : Good N S₀ ℓ) (h' : Good N S₀ ℓ'), Commute (Tgood S₀ hc ℓ h) (Tgood S₀ hc ℓ' h')

theorem isEigensystemH1_iff {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (lam : ℕ → K) :
    IsEigensystemH1 N ρ a S₀ lam ↔ ∃ x : coeffH1 ρ, x ≠ 0 ∧ IsEigvec S₀ hc lam x := by
  constructor
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun ℓ hg => ?_⟩
    obtain ⟨T, hT, hTx⟩ := h ℓ hg.1 hg.2.1 hg.2.2
    haveI : NeZero ℓ := hg.neZero
    have hT' : IsCoeffHeckeOnH1 N ℓ ρ (a ℓ) T := hT
    rw [eq_heckeH1_of_isCoeffHeckeOnH1 (hc ℓ hg) hT'] at hTx
    exact hTx
  · rintro ⟨x, hx, h⟩
    refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    exact ⟨Tgood S₀ hc ℓ ⟨hℓ, hℓN, hℓS⟩, isCoeffHeckeOnH1_heckeH1 _, h ℓ ⟨hℓ, hℓN, hℓS⟩⟩

theorem goodCommute_of_comm {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)}
    (hc : GoodCompat S₀ ρ a) (hcomm : ∀ ℓ ℓ', Good N S₀ ℓ → Good N S₀ ℓ' → a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ) :
    GoodCommute S₀ hc := by
  intro ℓ ℓ' h h'
  by_cases hne : ℓ = ℓ'
  · subst hne
    exact Commute.refl _
  refine LinearMap.ext fun x => ?_
  haveI := h.neZero
  haveI := h'.neZero
  exact heckeH1_comm h.1 h'.1 h.2.1 h'.2.1 hne (hc ℓ h) (hc ℓ' h') (hcomm ℓ ℓ' h h') x

end Systems

section Book

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N : ℕ) (ρ : Representation K (Gamma0 N) V)

theorem isEigensystemH1_congr (a : ℕ → (V →ₗ[K] V)) (S₀ : Set ℕ) {lam lam' : ℕ → K}
    (hll : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → lam ℓ = lam' ℓ) (h : IsEigensystemH1 N ρ a S₀ lam) :
    IsEigensystemH1 N ρ a S₀ lam' := by
  obtain ⟨x, hx, heig⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
  exact ⟨T, hT, by rw [hTx, hll ℓ hℓ hℓN hℓS]⟩

theorem isEigensystemH1_mono (a : ℕ → (V →ₗ[K] V)) {S₀ S₁ : Set ℕ} (hS : S₀ ⊆ S₁) {lam : ℕ → K}
    (h : IsEigensystemH1 N ρ a S₀ lam) : IsEigensystemH1 N ρ a S₁ lam := by
  obtain ⟨x, hx, heig⟩ := h
  exact ⟨x, hx, fun ℓ hℓ hℓN hℓS => heig ℓ hℓ hℓN fun h' => hℓS (hS h')⟩

end Book

section Entries

variable (M : ℕ)

def a3 (γ : Gamma0 M) : ZMod 3 := (((γ : SL(2, ℤ)) 0 0 : ℤ) : ZMod 3)
def b3 (γ : Gamma0 M) : ZMod 3 := (((γ : SL(2, ℤ)) 0 1 : ℤ) : ZMod 3)
def d3 (γ : Gamma0 M) : ZMod 3 := (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod 3)

def phi (γ : Gamma0 M) : ZMod 3 := b3 M γ * d3 M γ

theorem entry_c_dvd (γ : Gamma0 M) : (M : ℤ) ∣ (γ : SL(2, ℤ)) 1 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (Gamma0_mem.mp γ.2)

theorem zmod3_mul_self {a : ZMod 3} (ha : a ≠ 0) : a * a = 1 := by
  fin_cases a
  · exact absurd rfl ha
  · rfl
  · rfl

variable (h3M : 3 ∣ M)
include h3M

theorem c3_eq_zero (γ : Gamma0 M) : ((((γ : SL(2, ℤ)) 1 0 : ℤ)) : ZMod 3) = 0 := by
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact (Int.natCast_dvd_natCast.mpr h3M).trans (entry_c_dvd M γ)

theorem a3_mul_d3 (γ : Gamma0 M) : a3 M γ * d3 M γ = 1 := by
  have hdet := Matrix.det_fin_two ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
  rw [(γ : SL(2, ℤ)).2] at hdet
  have h := congrArg (fun x : ℤ => (x : ZMod 3)) hdet
  simp only [Int.cast_one, Int.cast_sub, Int.cast_mul, c3_eq_zero M h3M γ, mul_zero, sub_zero] at h
  exact h.symm

theorem d3_ne_zero (γ : Gamma0 M) : d3 M γ ≠ 0 := fun h => by
  have := a3_mul_d3 M h3M γ
  rw [h, mul_zero] at this
  exact zero_ne_one this

theorem d3_mul_d3 (γ : Gamma0 M) : d3 M γ * d3 M γ = 1 := zmod3_mul_self (d3_ne_zero M h3M γ)

theorem d3_mul (γ γ' : Gamma0 M) : d3 M (γ * γ') = d3 M γ * d3 M γ' := by
  simp only [d3]
  rw [show (((γ * γ' : Gamma0 M) : SL(2, ℤ)) 1 1 : ℤ)
      = (γ : SL(2, ℤ)) 1 0 * (γ' : SL(2, ℤ)) 0 1 + (γ : SL(2, ℤ)) 1 1 * (γ' : SL(2, ℤ)) 1 1 from
      (Matrix.two_mul_expl ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (γ' : SL(2, ℤ))).2.2.2]
  push_cast
  rw [c3_eq_zero M h3M γ, zero_mul, zero_add]

omit h3M in
theorem b3_mul (γ γ' : Gamma0 M) : b3 M (γ * γ') = a3 M γ * b3 M γ' + b3 M γ * d3 M γ' := by
  simp only [a3, b3, d3]
  rw [show (((γ * γ' : Gamma0 M) : SL(2, ℤ)) 0 1 : ℤ)
      = (γ : SL(2, ℤ)) 0 0 * (γ' : SL(2, ℤ)) 0 1 + (γ : SL(2, ℤ)) 0 1 * (γ' : SL(2, ℤ)) 1 1 from
      (Matrix.two_mul_expl ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) (γ' : SL(2, ℤ))).2.1]
  push_cast
  ring

theorem phi_mul (γ γ' : Gamma0 M) : phi M (γ * γ') = phi M γ + phi M γ' := by
  rw [phi, phi, phi, b3_mul, d3_mul M h3M]
  have h1 := a3_mul_d3 M h3M γ
  have h2 := d3_mul_d3 M h3M γ'
  linear_combination (b3 M γ' * d3 M γ') * h1 + (b3 M γ * d3 M γ) * h2

omit h3M in
theorem phi_one : phi M 1 = 0 := by simp [phi, b3]

theorem phi_inv (γ : Gamma0 M) : phi M γ⁻¹ = -phi M γ := by
  have h := phi_mul M h3M γ⁻¹ γ
  rw [inv_mul_cancel, phi_one] at h
  linear_combination (-1 : ZMod 3) * h

theorem phi_eq_zero_iff (γ : Gamma0 M) : phi M γ = 0 ↔ (3 : ℤ) ∣ (γ : SL(2, ℤ)) 0 1 := by
  rw [phi, mul_eq_zero, or_iff_left (d3_ne_zero M h3M γ), b3]
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3)

omit h3M in

theorem natCast_mul_phi_heckeConj (ℓ : ℕ) [NeZero ℓ] (u : ↥(heckeUpper M ℓ)) :
    (ℓ : ZMod 3) * phi M (heckeConj M ℓ u) = phi M (u : Gamma0 M) := by
  have hb : (ℓ : ZMod 3) * b3 M (heckeConj M ℓ u) = b3 M (u : Gamma0 M) := by
    simp only [b3]
    change (ℓ : ZMod 3) * (((((u : Gamma0 M) : SL(2, ℤ)) 0 1 / (ℓ : ℤ) : ℤ)) : ZMod 3) = _
    have h := Int.ediv_mul_cancel ((mem_heckeUpper M ℓ).mp u.2)
    rw [mul_comm, ← Int.cast_natCast (R := ZMod 3) ℓ, ← Int.cast_mul, h]
  have hd : d3 M (heckeConj M ℓ u) = d3 M (u : Gamma0 M) := rfl
  rw [phi, phi, ← hb, hd]
  ring

omit h3M in
theorem phi_heckeConj {ℓ : ℕ} [NeZero ℓ] (hℓ : (ℓ : ZMod 3) ≠ 0) (u : ↥(heckeUpper M ℓ)) :
    phi M (heckeConj M ℓ u) = (ℓ : ZMod 3) * phi M (u : Gamma0 M) := by
  rw [← natCast_mul_phi_heckeConj M ℓ u, ← mul_assoc, zmod3_mul_self hℓ, one_mul]

omit h3M in

def Tg : Gamma0 M := ⟨ModularGroup.T, by rw [Gamma0_mem, ModularGroup.T]; simp⟩

omit h3M in
theorem coe_Tg_zpow (n : ℤ) : (((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) = !![1, n; 0, 1] := by
  rw [show ((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) = ModularGroup.T ^ n from rfl]
  exact ModularGroup.coe_T_zpow n

omit h3M in
theorem Tg_zpow_zero_one (n : ℤ) : (((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) 0 1 : ℤ) = n := by
  rw [show ((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) 0 1 = (!![(1 : ℤ), n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 0 1 from
    congrFun (congrFun (coe_Tg_zpow M n) 0) 1]
  simp

omit h3M in
theorem phi_Tg_zpow (n : ℤ) : phi M (Tg M ^ n) = (n : ZMod 3) := by
  simp only [phi, b3, d3]
  rw [Tg_zpow_zero_one,
    show ((Tg M ^ n : Gamma0 M) : SL(2, ℤ)) 1 1 = (!![(1 : ℤ), n; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) 1 1 from
      congrFun (congrFun (coe_Tg_zpow M n) 1) 1]
  simp

omit h3M in
theorem phi_Tg : phi M (Tg M) = 1 := by
  have := phi_Tg_zpow M 1
  rwa [zpow_one, Int.cast_one] at this

theorem natCast_zmod_ne_zero {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) : (ℓ : ZMod 3) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  intro h
  have h3 : (3 : ℕ) ∣ M := h3M
  exact hℓM (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp h) ▸ h3)

theorem three_dvd_Tg_zpow_neg_mul (γ : Gamma0 M) :
    (3 : ℤ) ∣ ((Tg M ^ (-((phi M γ).val : ℤ)) * γ : Gamma0 M) : SL(2, ℤ)) 0 1 := by
  rw [← phi_eq_zero_iff M h3M, phi_mul M h3M, phi_Tg_zpow]
  push_cast
  rw [ZMod.natCast_zmod_val, neg_add_cancel]

end Entries

section W

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type*) [CommRing κ]

variable [CharP κ 3] in

noncomputable abbrev cst : ZMod 3 →+* κ := ZMod.castHom (dvd_refl 3) κ

def rhoFun (γ : Gamma0 M) : (ZMod 3 → κ) →ₗ[κ] (ZMod 3 → κ) where
  toFun f u := f (u + phi M γ)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem rhoFun_apply (γ : Gamma0 M) (f : ZMod 3 → κ) (u : ZMod 3) : rhoFun M κ γ f u = f (u + phi M γ) := rfl

def rhoW : Representation κ (Gamma0 M) (ZMod 3 → κ) where
  toFun := rhoFun M κ
  map_one' := by
    refine LinearMap.ext fun f => funext fun u => ?_
    rw [rhoFun_apply, phi_one, add_zero, Module.End.one_apply]
  map_mul' γ γ' := by
    refine LinearMap.ext fun f => funext fun u => ?_
    rw [Module.End.mul_apply, rhoFun_apply, rhoFun_apply, rhoFun_apply, phi_mul M h3M, add_assoc]

@[scoped simp] theorem rhoW_apply (γ : Gamma0 M) (f : ZMod 3 → κ) (u : ZMod 3) :
    rhoW M h3M κ γ f u = f (u + phi M γ) := rfl

def aW (ℓ : ℕ) : (ZMod 3 → κ) →ₗ[κ] (ZMod 3 → κ) where
  toFun f u := f ((ℓ : ZMod 3) * u)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem aW_apply (ℓ : ℕ) (f : ZMod 3 → κ) (u : ZMod 3) : aW κ ℓ f u = f ((ℓ : ZMod 3) * u) := rfl

theorem aW_comm (ℓ ℓ' : ℕ) : aW κ ℓ ∘ₗ aW κ ℓ' = aW κ ℓ' ∘ₗ aW κ ℓ := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, aW_apply]
  ring_nf

theorem isCompat_W (ℓ : ℕ) [NeZero ℓ] (hℓ : (ℓ : ZMod 3) ≠ 0) : IsCompat M ℓ (rhoW M h3M κ) (aW κ ℓ) := by
  intro u
  refine LinearMap.ext fun f => funext fun w => ?_
  simp only [LinearMap.comp_apply, aW_apply, rhoW_apply, phi_heckeConj M hℓ]
  ring_nf

def sh (v : ZMod 3) : (ZMod 3 → κ) →ₗ[κ] (ZMod 3 → κ) where
  toFun f u := f (u + v)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem sh_apply (v : ZMod 3) (f : ZMod 3 → κ) (u : ZMod 3) : sh κ v f u = f (u + v) := rfl

theorem sh_rhoW (v : ZMod 3) (γ : Gamma0 M) : sh κ v ∘ₗ rhoW M h3M κ γ = rhoW M h3M κ γ ∘ₗ sh κ v := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, sh_apply, rhoW_apply]
  ring_nf

theorem aW_sh {ℓ : ℕ} (hℓ : (ℓ : ZMod 3) ≠ 0) (v : ZMod 3) :
    aW κ ℓ ∘ₗ sh κ v = sh κ ((ℓ : ZMod 3) * v) ∘ₗ aW κ ℓ := by
  refine LinearMap.ext fun f => funext fun u => ?_
  simp only [LinearMap.comp_apply, sh_apply, aW_apply]
  congr 1
  have := zmod3_mul_self hℓ
  linear_combination (-v) * this

def ev0 : (ZMod 3 → κ) →ₗ[κ] κ where
  toFun f := f 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[scoped simp] theorem ev0_apply (f : ZMod 3 → κ) : ev0 κ f = f 0 := rfl

theorem ev0_aW (ℓ : ℕ) : ev0 κ ∘ₗ aW κ ℓ = (1 : κ) • ev0 κ := by
  refine LinearMap.ext fun f => ?_
  simp

theorem ev0_rhoW (δ : Gamma0 M) (hδ : (3 : ℤ) ∣ (δ : SL(2, ℤ)) 0 1) :
    ev0 κ ∘ₗ rhoW M h3M κ δ = ev0 κ := by
  refine LinearMap.ext fun f => ?_
  have hb : phi M δ = 0 := (phi_eq_zero_iff M h3M δ).mpr hδ
  simp [hb]

end W

section Post

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable {N : ℕ} {ρ : Representation K (Gamma0 N) V}

theorem e_rho_apply (e : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e) (g : Gamma0 N) (v : V) :
    e (ρ g v) = ρ g (e v) := by
  have h := LinearMap.congr_fun (he g) v
  simpa only [LinearMap.comp_apply] using h

theorem post_mem_coeffCocycles (e : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e)
    {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρ) : (fun g => e (z g)) ∈ coeffCocycles ρ := by
  intro g h
  show e (z (g * h)) = e (z g) + ρ g (e (z h))
  rw [hz g h, map_add, e_rho_apply e he]

theorem post_mem_coeffCoboundaries (e : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e)
    {z : Gamma0 N → V} (hz : z ∈ coeffCoboundaries ρ) : (fun g => e (z g)) ∈ coeffCoboundaries ρ := by
  obtain ⟨v, rfl⟩ := hz
  refine ⟨e v, funext fun g => ?_⟩
  show ρ g (e v) - e v = e (ρ g v - v)
  rw [map_sub, e_rho_apply e he]

def postZ1 (e : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e) : ↥(coeffCocycles ρ) →ₗ[K] ↥(coeffCocycles ρ) where
  toFun z := ⟨fun g => e ((z : Gamma0 N → V) g), post_mem_coeffCocycles e he z.2⟩
  map_add' z w := by
    refine Subtype.ext (funext fun g => ?_)
    show e (((z + w : ↥(coeffCocycles ρ)) : Gamma0 N → V) g) = e ((z : Gamma0 N → V) g) + e ((w : Gamma0 N → V) g)
    rw [Submodule.coe_add, Pi.add_apply, map_add]
  map_smul' c z := by
    refine Subtype.ext (funext fun g => ?_)
    show e (((c • z : ↥(coeffCocycles ρ)) : Gamma0 N → V) g) = c • e ((z : Gamma0 N → V) g)
    rw [Submodule.coe_smul, Pi.smul_apply, map_smul]

theorem coe_postZ1 (e : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e) (z : ↥(coeffCocycles ρ)) (g : Gamma0 N) :
    (postZ1 e he z : Gamma0 N → V) g = e ((z : Gamma0 N → V) g) := rfl

def postH1 (e : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e) : coeffH1 ρ →ₗ[K] coeffH1 ρ :=
  ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype).mapQ
    ((coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype) (postZ1 e he)
    fun _ hz => post_mem_coeffCoboundaries e he hz

theorem postH1_mk (e : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e) (z : ↥(coeffCocycles ρ)) :
    postH1 e he (coeffH1Mk ρ z) = coeffH1Mk ρ (postZ1 e he z) := rfl

theorem heckeH1_postH1 {ℓ : ℕ} [NeZero ℓ] {a : V →ₗ[K] V} (ha : IsCompat N ℓ ρ a)
    (e e' : V →ₗ[K] V) (he : ∀ g, e ∘ₗ ρ g = ρ g ∘ₗ e) (he' : ∀ g, e' ∘ₗ ρ g = ρ g ∘ₗ e')
    (hae : a ∘ₗ e = e' ∘ₗ a) (x : coeffH1 ρ) :
    heckeH1 ha (postH1 e he x) = postH1 e' he' (heckeH1 ha x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [postH1_mk, heckeH1_mk, heckeH1_mk, postH1_mk]
  congr 1
  refine Subtype.ext (funext fun g => ?_)
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  rw [coe_heckeZ1, coe_postZ1, coe_heckeZ1, coeffHeckeFun_apply, coeffHeckeFun_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coe_postZ1]
  have h1 := LinearMap.congr_fun hae ((z : Gamma0 N → V) (heckeConj N ℓ (transferAux (heckeUpper N ℓ) g q)))
  simp only [LinearMap.comp_apply] at h1
  rw [h1, e_rho_apply e' he']

end Post

section Cocycles

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type*) [CommRing κ] [CharP κ 3]
variable (x : Additive (Gamma0 M) →+ κ)

def Zr : Gamma0 M → ZMod 3 → κ := fun γ _ => x (Additive.ofMul γ)

omit [CharP κ 3] in
theorem Zr_mem : Zr M κ x ∈ coeffCocycles (rhoW M h3M κ) := by
  intro g h
  funext u
  simp [Zr]

noncomputable def Z1 (H : Gamma0 M → κ) : Gamma0 M → ZMod 3 → κ := fun γ u => H γ + cst κ u * x (Additive.ofMul γ)

theorem cst_phi (γ : Gamma0 M) :
    cst κ (phi M γ) = ((((γ : SL(2, ℤ)) 0 1) * ((γ : SL(2, ℤ)) 1 1) : ℤ) : κ) := by
  rw [phi, b3, d3, ← Int.cast_mul, map_intCast]

theorem Z1_mem (H : Gamma0 M → κ)
    (hH : ∀ γ γ' : Gamma0 M, H (γ * γ') = H γ + H γ' +
      ((((γ : SL(2, ℤ)) 0 1) * ((γ : SL(2, ℤ)) 1 1) : ℤ) : κ) * x (Additive.ofMul γ')) :
    Z1 M κ x H ∈ coeffCocycles (rhoW M h3M κ) := by
  intro g h
  funext u
  simp only [Z1, Pi.add_apply, rhoW_apply, hH, ← cst_phi M, ofMul_mul, map_add]
  ring

theorem sh_Z1 (H : Gamma0 M → κ) (γ : Gamma0 M) :
    sh κ 2 (Z1 M κ x H γ) - sh κ 1 (Z1 M κ x H γ) = Zr M κ x γ := by
  funext u
  simp only [Pi.sub_apply, sh_apply, Z1, Zr, map_add]
  have h1 : cst κ (2 : ZMod 3) - cst κ 1 = 1 := by
    rw [← map_sub]; exact (map_one (cst κ))
  linear_combination (x (Additive.ofMul γ)) * h1

omit [CharP κ 3] in

theorem heckeFun_Zr (ℓ : ℕ) [NeZero ℓ] (nu : κ) (hx : heckeOperatorHom M ℓ κ x = nu • x) :
    coeffHeckeFun M ℓ (rhoW M h3M κ) (aW κ ℓ) (Zr M κ x) = nu • Zr M κ x := by
  letI := (heckeUpper M ℓ).fintypeQuotientOfFiniteIndex
  funext g u
  rw [coeffHeckeFun_apply, Finset.sum_apply]
  simp only [rhoW_apply, aW_apply, Zr, Pi.smul_apply, smul_eq_mul]
  have h := heckeOperatorHom_apply M ℓ κ x g
  rw [hx, AddMonoidHom.smul_apply, smul_eq_mul] at h
  exact h.symm

omit [CharP κ 3] in
theorem cocycle_one {z : Gamma0 M → ZMod 3 → κ} (hz : z ∈ coeffCocycles (rhoW M h3M κ)) : z 1 = 0 := by
  have h := hz 1 1
  rw [mul_one, map_one, Module.End.one_apply] at h
  have : z 1 + z 1 = z 1 + 0 := by rw [add_zero]; exact h.symm
  exact add_left_cancel this

omit [CharP κ 3] in

theorem mem_coeffCoboundaries_of_forall_apply_zero {z : Gamma0 M → ZMod 3 → κ}
    (hz : z ∈ coeffCocycles (rhoW M h3M κ))
    (h0 : ∀ h : Gamma0 M, (3 : ℤ) ∣ (h : SL(2, ℤ)) 0 1 → z h 0 = 0) :
    z ∈ coeffCoboundaries (rhoW M h3M κ) := by

  have hT0 : ∀ n : ℤ, (n : ZMod 3) = 0 → z (Tg M ^ n) 0 = 0 := by
    intro n hn
    apply h0
    rw [Tg_zpow_zero_one]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd n 3).mp hn

  have hTT : ∀ m n : ℤ, z (Tg M ^ (m + n)) 0 = z (Tg M ^ m) 0 + z (Tg M ^ n) (m : ZMod 3) := by
    intro m n
    rw [zpow_add, hz, Pi.add_apply, rhoW_apply, phi_Tg_zpow, zero_add]

  have hH' : ∀ δ : Gamma0 M, (3 : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → ∀ w : ZMod 3, z δ w = 0 := by
    intro δ hδ w
    have hφδ : phi M δ = 0 := (phi_eq_zero_iff M h3M δ).mpr hδ
    set m : ℤ := (w.val : ℤ) with hm
    have hmw : (m : ZMod 3) = w := by rw [hm, Int.cast_natCast, ZMod.natCast_zmod_val]
    set δ' : Gamma0 M := Tg M ^ m * δ * Tg M ^ (-m) with hδ'
    have hφδ' : phi M δ' = 0 := by
      rw [hδ', phi_mul M h3M, phi_mul M h3M, hφδ, phi_Tg_zpow, phi_Tg_zpow]; push_cast; ring
    have hδ'0 : z δ' 0 = 0 := h0 δ' ((phi_eq_zero_iff M h3M δ').mp hφδ')
    have heq : δ' * Tg M ^ m = Tg M ^ m * δ := by rw [hδ']; group
    have h1 := hz δ' (Tg M ^ m)
    have h2 := hz (Tg M ^ m) δ
    rw [heq] at h1
    have h3 := congrFun (h1.symm.trans h2) 0
    simp only [Pi.add_apply, rhoW_apply, hφδ', hδ'0, phi_Tg_zpow, hmw, zero_add, add_zero] at h3

    have : z (Tg M ^ m) 0 + z δ w = z (Tg M ^ m) 0 + 0 := by rw [add_zero]; exact h3.symm
    exact add_left_cancel this

  let f : ZMod 3 → κ := fun u => z (Tg M ^ (u.val : ℤ)) 0
  have hf : ∀ (u : ZMod 3) (n : ℤ), z (Tg M ^ n) u = f (u + n) - f u := by
    intro u n
    have hu : (((u.val : ℤ)) : ZMod 3) = u := by rw [Int.cast_natCast, ZMod.natCast_zmod_val]
    have h1 := hTT (u.val : ℤ) n
    rw [hu] at h1

    set k : ℤ := (u.val : ℤ) + n - (((u + n).val : ℤ)) with hk
    have hk0 : (k : ZMod 3) = 0 := by
      rw [hk]; push_cast; rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]; ring
    have h2 : z (Tg M ^ ((u.val : ℤ) + n)) 0 = f (u + n) := by
      have : (u.val : ℤ) + n = k + (((u + n).val : ℤ)) := by rw [hk]; ring
      rw [this, hTT, hT0 k hk0, hk0, zero_add]
    rw [h2] at h1
    change z (Tg M ^ n) u = f (u + n) - z (Tg M ^ (u.val : ℤ)) 0
    rw [h1]; ring
  refine (mem_coeffCoboundaries_iff _ _).mpr ⟨f, funext fun γ => funext fun u => ?_⟩

  set n : ℤ := ((phi M γ).val : ℤ) with hn
  have hnφ : (n : ZMod 3) = phi M γ := by rw [hn, Int.cast_natCast, ZMod.natCast_zmod_val]
  set δ : Gamma0 M := Tg M ^ (-n) * γ with hδ
  have hδmem : (3 : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 := three_dvd_Tg_zpow_neg_mul M h3M γ
  have hγ : γ = Tg M ^ n * δ := by rw [hδ, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  change rhoW M h3M κ γ f u - f u = z γ u
  rw [rhoW_apply, hγ, hz, Pi.add_apply, rhoW_apply, hH' δ hδmem, add_zero, phi_mul M h3M, phi_Tg_zpow,
    (phi_eq_zero_iff M h3M δ).mpr hδmem, add_zero, hf, hnφ]

end Cocycles

section Eisenstein

variable (M : ℕ) (h3M : 3 ∣ M) (κ : Type*) [CommRing κ] [CharP κ 3]
variable (x : Additive (Gamma0 M) →+ κ)

include h3M in

theorem apply_eq_cst_phi_mul (hx : ∀ δ : Gamma0 M, (3 : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → x (Additive.ofMul δ) = 0)
    (γ : Gamma0 M) : x (Additive.ofMul γ) = cst κ (phi M γ) * x (Additive.ofMul (Tg M)) := by
  set n : ℤ := ((phi M γ).val : ℤ) with hn
  have hnφ : (n : ZMod 3) = phi M γ := by rw [hn, Int.cast_natCast, ZMod.natCast_zmod_val]
  set δ : Gamma0 M := Tg M ^ (-n) * γ with hδ
  have hδmem : (3 : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 := three_dvd_Tg_zpow_neg_mul M h3M γ
  have hγ : γ = Tg M ^ n * δ := by rw [hδ, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  conv_lhs => rw [hγ, ofMul_mul, map_add, hx δ hδmem, add_zero, ofMul_zpow, map_zsmul, zsmul_eq_mul]
  rw [← hnφ, map_intCast]

include h3M in

theorem heckeOperatorHom_eq_of_vanish (hx : ∀ δ : Gamma0 M, (3 : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → x (Additive.ofMul δ) = 0)
    {ℓ : ℕ} [NeZero ℓ] (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M) :
    heckeOperatorHom M ℓ κ x = ((ℓ : κ) * ((ℓ : κ) + 1)) • x := by
  letI := (heckeUpper M ℓ).fintypeQuotientOfFiniteIndex
  have hℓ3 : (ℓ : ZMod 3) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have h3 : (3 : ℕ) ∣ M := h3M
    exact hℓM (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).mp h) ▸ h3)
  have hcard : Fintype.card (Gamma0 M ⧸ heckeUpper M ℓ) = ℓ + 1 := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index, ModularCurve.index_heckeUpper hℓ hℓM]
  refine AddMonoidHom.ext fun g' => ?_
  set g : Gamma0 M := Additive.toMul g' with hg
  have hg' : g' = Additive.ofMul g := rfl
  rw [hg', heckeOperatorHom_apply, AddMonoidHom.smul_apply, smul_eq_mul]
  have hterm : ∀ q : Gamma0 M ⧸ heckeUpper M ℓ,
      x (Additive.ofMul (heckeConj M ℓ (transferAux (heckeUpper M ℓ) g q) : Gamma0 M))
        = (ℓ : κ) * cst κ (phi M (transferAux (heckeUpper M ℓ) g q : Gamma0 M)) * x (Additive.ofMul (Tg M)) := by
    intro q
    rw [apply_eq_cst_phi_mul M h3M κ x hx, phi_heckeConj M hℓ3, map_mul, map_natCast]
  simp only [hterm]
  rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum]

  have hsum : ∑ q : Gamma0 M ⧸ heckeUpper M ℓ, phi M (transferAux (heckeUpper M ℓ) g q : Gamma0 M)
      = ((ℓ + 1 : ℕ) : ZMod 3) * phi M g := by
    have hq : ∀ q : Gamma0 M ⧸ heckeUpper M ℓ, phi M (transferAux (heckeUpper M ℓ) g q : Gamma0 M)
        = phi M g + phi M q.out - phi M (g • q).out := by
      intro q
      rw [show ((transferAux (heckeUpper M ℓ) g q : ↥(heckeUpper M ℓ)) : Gamma0 M) = (g • q).out⁻¹ * (g * q.out)
        from rfl, phi_mul M h3M, phi_mul M h3M, phi_inv M h3M]
      ring
    simp only [hq, Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, hcard,
      nsmul_eq_mul]
    rw [Fintype.sum_bijective (g • ·) (MulAction.bijective g)
      (fun q : Gamma0 M ⧸ heckeUpper M ℓ => phi M (g • q).out) (fun q : Gamma0 M ⧸ heckeUpper M ℓ => phi M q.out)
      fun q => rfl]
    ring
  rw [hsum, map_mul, map_natCast, apply_eq_cst_phi_mul M h3M κ x hx g]
  push_cast
  ring

end Eisenstein

section Final

variable (M : ℕ) [NeZero M] (h3M : 3 ∣ M) (κ : Type) [Field κ] [CharP κ 3] (S₀ : Set ℕ)

omit [NeZero M] [CharP κ 3] in

theorem final {τ : ℕ → κ} (hτ : IsEigensystemH1 M (rhoW M h3M κ) (aW κ) S₀ τ) :
    IsEigensystemH1 (M * 3) (1 : Representation κ (Gamma0 (M * 3)) κ) (fun _ => LinearMap.id) (insert 3 S₀) τ := by
  obtain ⟨xc, hx, heig⟩ := hτ
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ xc
  obtain ⟨y, hy1, hy2⟩ := HeckeEis.exists_addMonoidHom_functional_cocycle_smul_heckeOperatorHom_mul_eq 3 M
    (rhoW M h3M κ) (aW κ) (ev0 κ) (fun _ => (1 : κ)) (ev0_rhoW M h3M κ) (ev0_aW κ)
    (z : Gamma0 M → ZMod 3 → κ) z.2

  have hy0 : y ≠ 0 := by
    intro hy
    apply hx
    rw [coeffH1Mk_eq_zero_iff]
    refine mem_coeffCoboundaries_of_forall_apply_zero M h3M κ z.2 fun h hh => ?_
    let u : ↥(heckeUpper M 3) := ⟨h, (mem_heckeUpper M 3).mpr hh⟩
    have hmem : heckeConjSL M 3 u ∈ Gamma0 (M * 3) := by
      rw [Gamma0_mem]
      show (((heckeConjMat 3 ((h : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) 1 0 : ℤ) : ZMod (M * 3)) = 0
      rw [heckeConjMat_apply_one_zero, ZMod.intCast_zmod_eq_zero_iff_dvd]
      push_cast
      exact mul_dvd_mul_right (entry_c_dvd M h) _
    have hrel := hy1 ⟨heckeConjSL M 3 u, hmem⟩ h (heckeConjMat_mul_alphaMat hh)
    rw [hy, AddMonoidHom.zero_apply] at hrel
    exact hrel.symm

  let zy : Gamma0 (M * 3) → κ := fun g => y (Additive.ofMul g)
  have hzy : zy ∈ coeffCocycles (1 : Representation κ (Gamma0 (M * 3)) κ) := by
    intro g h
    change y (Additive.ofMul (g * h)) = y (Additive.ofMul g) + y (Additive.ofMul h)
    rw [ofMul_mul, map_add]
  refine ⟨coeffH1Mk _ ⟨zy, hzy⟩, ?_, fun ℓ hℓ hℓM3 hℓS => ?_⟩
  · intro h0
    rw [coeffH1Mk_eq_zero_iff] at h0
    obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp h0
    apply hy0
    refine AddMonoidHom.ext fun g => ?_
    have := congrFun hv (Additive.toMul g)
    simp only [MonoidHom.one_apply, Module.End.one_apply, sub_self] at this
    change y (Additive.ofMul (Additive.toMul g)) = 0
    exact this.symm
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have hℓM : ¬ ℓ ∣ M := fun h => hℓM3 (h.mul_right 3)
    have hℓ3 : ℓ ≠ 3 := fun h => hℓM3 (h ▸ dvd_mul_left 3 M)
    have hℓS' : ℓ ∉ S₀ := fun h => hℓS (Set.mem_insert_of_mem 3 h)
    have hcompat : IsCompat (M * 3) ℓ (1 : Representation κ (Gamma0 (M * 3)) κ) LinearMap.id := by
      intro u; simp
    refine ⟨heckeH1 hcompat, isCoeffHeckeOnH1_heckeH1 hcompat, ?_⟩
    obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓM hℓS'
    have hTy : heckeOperatorHom (M * 3) ℓ κ y = τ ℓ • y := by
      have h := hy2 ℓ hℓ hℓM hℓ3 (isCompat_W M h3M κ ℓ (natCast_zmod_ne_zero M h3M hℓ hℓM)) (τ ℓ) T hT hTx
      rwa [one_smul] at h
    rw [heckeH1_mk, ← map_smul]
    congr 1
    refine Subtype.ext (funext fun g => ?_)
    change coeffHeckeFun (M * 3) ℓ (1 : Representation κ (Gamma0 (M * 3)) κ) LinearMap.id
        (fun h => y (Additive.ofMul h)) g = τ ℓ * y (Additive.ofMul g)
    rw [coeffHeckeFun_trivial, hTy, AddMonoidHom.smul_apply, smul_eq_mul]

end Final

section Main

variable (M : ℕ) [NeZero M] (h3M : 3 ∣ M) (S₀ : Set ℕ) (κ : Type) [Field κ] [CharP κ 3] (nu : ℕ → κ)

omit [NeZero M] [CharP κ 3] in

theorem unpack (hocc : IsEigensystemH1 M (1 : Representation κ (Gamma0 M) κ) (fun _ => LinearMap.id) S₀ nu) :
    ∃ x : Additive (Gamma0 M) →+ κ, x ≠ 0 ∧ ∀ (ℓ : ℕ) (hℓ : ℓ.Prime), ¬ ℓ ∣ M → ℓ ∉ S₀ →
      (haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩; heckeOperatorHom M ℓ κ x = nu ℓ • x) := by
  obtain ⟨xc, hxc, heig⟩ := hocc
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ xc
  have hz := z.2
  let x : Additive (Gamma0 M) →+ κ := AddMonoidHom.mk' (fun a => (z : Gamma0 M → κ) (Additive.toMul a))
    (fun a b => by
      change (z : Gamma0 M → κ) (Additive.toMul a * Additive.toMul b) = _
      rw [hz]; simp)
  have hxz : (fun h => x (Additive.ofMul h)) = (z : Gamma0 M → κ) := rfl
  refine ⟨x, fun hx0 => hxc ?_, fun ℓ hℓ hℓM hℓS => ?_⟩
  · rw [coeffH1Mk_eq_zero_iff]
    have : (z : Gamma0 M → κ) = 0 := by
      rw [← hxz]; funext h; rw [hx0]; rfl
    rw [this]; exact Submodule.zero_mem _
  · haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓM hℓS
    have hcompat : IsCompat M ℓ (1 : Representation κ (Gamma0 M) κ) LinearMap.id := by intro u; simp
    have hT' : IsCoeffHeckeOnH1 M ℓ (1 : Representation κ (Gamma0 M) κ) LinearMap.id T := hT
    rw [eq_heckeH1_of_isCoeffHeckeOnH1 hcompat hT', heckeH1_mk, ← map_smul, coeffH1Mk_eq_iff] at hTx
    obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff _ _).mp hTx
    have hfun : coeffHeckeFun M ℓ (1 : Representation κ (Gamma0 M) κ) LinearMap.id (z : Gamma0 M → κ)
        = nu ℓ • (z : Gamma0 M → κ) := by
      have : (fun g : Gamma0 M => (1 : Representation κ (Gamma0 M) κ) g v - v) = 0 := by
        funext g; simp
      rw [this] at hv
      exact (sub_eq_zero.mp hv.symm)
    refine AddMonoidHom.ext fun g' => ?_
    rw [show g' = Additive.ofMul (Additive.toMul g') from rfl, ← coeffHeckeFun_trivial, hxz, hfun]
    rfl

include h3M in

theorem main (hocc : IsEigensystemH1 M (1 : Representation κ (Gamma0 M) κ) (fun _ => LinearMap.id) S₀ nu) :
    ∃ M' : ℕ, M ∣ M' ∧ M' ∣ M * 3 ∧
      IsEigensystemH1 M' (1 : Representation κ (Gamma0 M') κ) (fun _ => LinearMap.id) (insert 3 S₀)
        (fun ℓ => (ℓ : κ) * nu ℓ) := by
  obtain ⟨x, hx0, hTx⟩ := unpack M S₀ κ nu hocc
  have h3κ : (3 : κ) = 0 := by simpa using CharP.cast_eq_zero κ 3

  have hℓsq : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ M → (ℓ : κ) * (ℓ : κ) = 1 := by
    intro ℓ hℓ hℓM
    have h := congrArg (cst κ) (zmod3_mul_self (natCast_zmod_ne_zero M h3M hℓ hℓM))
    rwa [map_mul, map_natCast, map_one] at h
  by_cases hEis : ∀ δ : Gamma0 M, (3 : ℤ) ∣ (δ : SL(2, ℤ)) 0 1 → x (Additive.ofMul δ) = 0
  ·
    refine ⟨M, dvd_rfl, dvd_mul_right M 3, ?_⟩
    refine isEigensystemH1_mono M _ _ (Set.subset_insert 3 S₀) (isEigensystemH1_congr M _ _ S₀ ?_ hocc)
    intro ℓ hℓ hℓM hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    have h1 := hTx ℓ hℓ hℓM hℓS
    have h2 := heckeOperatorHom_eq_of_vanish M h3M κ x hEis hℓ hℓM
    rw [h1] at h2

    have hxT : x (Additive.ofMul (Tg M)) ≠ 0 := by
      intro h0
      apply hx0
      refine AddMonoidHom.ext fun g => ?_
      rw [show g = Additive.ofMul (Additive.toMul g) from rfl, apply_eq_cst_phi_mul M h3M κ x hEis, h0, mul_zero]
      rfl
    have h3 := congrArg (fun f : Additive (Gamma0 M) →+ κ => f (Additive.ofMul (Tg M))) h2
    simp only [AddMonoidHom.smul_apply, smul_eq_mul] at h3
    have hnu : nu ℓ = (ℓ : κ) * ((ℓ : κ) + 1) := mul_right_cancel₀ hxT h3
    rw [hnu]
    have := hℓsq ℓ hℓ hℓM
    linear_combination (-(ℓ : κ)) * this
  ·
    refine ⟨M * 3, dvd_mul_right M 3, dvd_rfl, final M h3M κ S₀ ?_⟩

    obtain ⟨H, hH⟩ := HeckeEis.exists_map_mul_eq_add_add_upperRightMulLowerRight_mul_of_three_dvd M h3M κ x
    let zr : ↥(coeffCocycles (rhoW M h3M κ)) := ⟨Zr M κ x, Zr_mem M h3M κ x⟩
    let z1 : ↥(coeffCocycles (rhoW M h3M κ)) := ⟨Z1 M κ x H, Z1_mem M h3M κ x H hH⟩

    have hzr : coeffH1Mk (rhoW M h3M κ) zr ≠ 0 := by
      intro h0
      rw [coeffH1Mk_eq_zero_iff] at h0
      obtain ⟨f, hf⟩ := (mem_coeffCoboundaries_iff _ _).mp h0
      apply hEis
      intro δ hδ
      have h1 : (rhoW M h3M κ δ f - f) 0 = Zr M κ x δ 0 := congrFun (congrFun hf δ) 0
      rw [Pi.sub_apply, rhoW_apply, (phi_eq_zero_iff M h3M δ).mpr hδ, add_zero, sub_self] at h1
      exact h1.symm

    have hgood3 : ∀ ℓ, Good M S₀ ℓ → (ℓ : ZMod 3) ≠ 0 := fun ℓ hg => natCast_zmod_ne_zero M h3M hg.1 hg.2.1
    have hc : GoodCompat S₀ (rhoW M h3M κ) (aW κ) := fun ℓ hg => by
      haveI := hg.neZero
      exact isCompat_W M h3M κ ℓ (hgood3 ℓ hg)
    have hcomm : GoodCommute S₀ hc := goodCommute_of_comm S₀ hc fun ℓ ℓ' _ _ => aW_comm κ ℓ ℓ'

    have hsh : ∀ v : ZMod 3, ∀ g : Gamma0 M, sh κ v ∘ₗ (rhoW M h3M κ) g = (rhoW M h3M κ) g ∘ₗ sh κ v := fun v g => sh_rhoW M h3M κ v g
    let Ntw : coeffH1 (rhoW M h3M κ) →ₗ[κ] coeffH1 (rhoW M h3M κ) := postH1 (sh κ 2) (hsh 2) - postH1 (sh κ 1) (hsh 1)
    have hN1 : Ntw (coeffH1Mk (rhoW M h3M κ) z1) = coeffH1Mk (rhoW M h3M κ) zr := by
      change postH1 (sh κ 2) (hsh 2) (coeffH1Mk (rhoW M h3M κ) z1) - postH1 (sh κ 1) (hsh 1) (coeffH1Mk (rhoW M h3M κ) z1) = _
      rw [postH1_mk, postH1_mk, ← map_sub]
      congr 1
      refine Subtype.ext (funext fun γ => ?_)
      exact sh_Z1 M κ x H γ

    have hNT : ∀ (ℓ : ℕ) (hg : Good M S₀ ℓ) (w : coeffH1 (rhoW M h3M κ)),
        Tgood S₀ hc ℓ hg (Ntw w) = (ℓ : κ) • Ntw (Tgood S₀ hc ℓ hg w) := by
      intro ℓ hg w
      haveI := hg.neZero
      have hℓ0 := hgood3 ℓ hg
      change heckeH1 (hc ℓ hg) (postH1 (sh κ 2) (hsh 2) w - postH1 (sh κ 1) (hsh 1) w)
        = (ℓ : κ) • (postH1 (sh κ 2) (hsh 2) (heckeH1 (hc ℓ hg) w) - postH1 (sh κ 1) (hsh 1) (heckeH1 (hc ℓ hg) w))
      rw [map_sub, heckeH1_postH1 (hc ℓ hg) (sh κ 2) (sh κ ((ℓ : ZMod 3) * 2)) (hsh 2) (hsh _) (aW_sh κ hℓ0 2),
        heckeH1_postH1 (hc ℓ hg) (sh κ 1) (sh κ ((ℓ : ZMod 3) * 1)) (hsh 1) (hsh _) (aW_sh κ hℓ0 1)]

      have hcases : (ℓ : ZMod 3) = 1 ∨ (ℓ : ZMod 3) = 2 := by
        generalize (ℓ : ZMod 3) = a at hℓ0
        fin_cases a
        · exact absurd rfl hℓ0
        · exact Or.inl rfl
        · exact Or.inr rfl
      have hℓκ : (ℓ : κ) = cst κ (ℓ : ZMod 3) := (map_natCast (cst κ) ℓ).symm
      rcases hcases with h1 | h2
      · have e1 : (ℓ : κ) = 1 := by rw [hℓκ, h1, map_one]
        simp only [h1, e1, one_mul, mul_one, one_smul]
      · have e2 : (ℓ : κ) = -1 := by
          rw [hℓκ, h2, show (2 : ZMod 3) = -1 by rfl, map_neg, map_one]
        have e3 : (2 : ZMod 3) * 2 = 1 := by rfl
        have e4 : (2 : ZMod 3) * 1 = 2 := by rfl
        simp only [h2, e2, e3, e4, neg_smul, one_smul, neg_sub]

    have hTzr : ∀ (ℓ : ℕ) (hg : Good M S₀ ℓ), Tgood S₀ hc ℓ hg (coeffH1Mk (rhoW M h3M κ) zr) = nu ℓ • coeffH1Mk (rhoW M h3M κ) zr := by
      intro ℓ hg
      haveI := hg.neZero
      change heckeH1 (hc ℓ hg) (coeffH1Mk (rhoW M h3M κ) zr) = _
      rw [heckeH1_mk, ← map_smul]
      congr 1
      refine Subtype.ext ?_
      rw [coe_heckeZ1, Submodule.coe_smul]
      exact heckeFun_Zr M h3M κ x ℓ (nu ℓ) (hTx ℓ hg.1 hg.2.1 hg.2.2)

    set σ : ℕ → κ := fun ℓ => (ℓ : κ) * nu ℓ with hσ
    have hkey : ∀ (ℓ : ℕ) (hg : Good M S₀ ℓ),
        Ntw (Tgood S₀ hc ℓ hg (coeffH1Mk (rhoW M h3M κ) z1) - σ ℓ • coeffH1Mk (rhoW M h3M κ) z1) = 0 := by
      intro ℓ hg
      have hℓ1 := hℓsq ℓ hg.1 hg.2.1
      have h1 : (ℓ : κ) • Ntw (Tgood S₀ hc ℓ hg (coeffH1Mk (rhoW M h3M κ) z1)) = nu ℓ • coeffH1Mk (rhoW M h3M κ) zr := by
        rw [← hNT ℓ hg, hN1, hTzr ℓ hg]
      have h2 : Ntw (Tgood S₀ hc ℓ hg (coeffH1Mk (rhoW M h3M κ) z1)) = ((ℓ : κ) * nu ℓ) • coeffH1Mk (rhoW M h3M κ) zr := by
        have := congrArg (fun w => (ℓ : κ) • w) h1
        simp only [smul_smul, hℓ1, one_smul] at this
        rw [this]
      rw [map_sub, map_smul, h2, hN1, hσ, sub_self]

    let ι := {ℓ : ℕ // Good M S₀ ℓ}
    let U : Submodule κ (coeffH1 (rhoW M h3M κ)) :=
      ⨅ i : ι, LinearMap.ker (Ntw ∘ₗ (Tgood S₀ hc i.1 i.2 - σ i.1 • LinearMap.id))
    have hmemU : ∀ w, w ∈ U ↔ ∀ i : ι, Ntw (Tgood S₀ hc i.1 i.2 w - σ i.1 • w) = 0 := by
      intro w
      simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply]
    have hz1U : coeffH1Mk (rhoW M h3M κ) z1 ∈ U := (hmemU _).mpr fun i => hkey i.1 i.2
    have hstab : ∀ (j : ι), ∀ w ∈ U, Tgood S₀ hc j.1 j.2 w ∈ U := by
      intro j w hw
      rw [hmemU] at hw ⊢
      intro i
      have hcij := (hcomm i.1 j.1 i.2 j.2).eq
      have e1 : Tgood S₀ hc i.1 i.2 (Tgood S₀ hc j.1 j.2 w) - σ i.1 • Tgood S₀ hc j.1 j.2 w
          = Tgood S₀ hc j.1 j.2 (Tgood S₀ hc i.1 i.2 w - σ i.1 • w) := by
        rw [map_sub, map_smul, ← Module.End.mul_apply, hcij, Module.End.mul_apply]
      rw [e1]

      have hℓ1 := hℓsq j.1 j.2.1 j.2.2.1
      have e2 : Ntw (Tgood S₀ hc j.1 j.2 (Tgood S₀ hc i.1 i.2 w - σ i.1 • w))
          = (j.1 : κ) • Tgood S₀ hc j.1 j.2 (Ntw (Tgood S₀ hc i.1 i.2 w - σ i.1 • w)) := by
        have := congrArg (fun v => (j.1 : κ) • v) (hNT j.1 j.2 (Tgood S₀ hc i.1 i.2 w - σ i.1 • w))
        simp only [smul_smul, hℓ1, one_smul] at this
        exact this.symm
      rw [e2, hw i, map_zero, smul_zero]
    let TU : ι → ↥U →ₗ[κ] ↥U := fun j => (Tgood S₀ hc j.1 j.2).restrict (hstab j)
    have hTU : ∀ i j : ι, Commute (TU i) (TU j) := fun i j =>
      LinearMap.ext fun w => Subtype.ext (LinearMap.congr_fun (hcomm i.1 j.1 i.2 j.2).eq (w : coeffH1 (rhoW M h3M κ)))
    let P : Submodule κ ↥U := (LinearMap.ker Ntw).comap U.subtype
    have hP : P ≠ ⊤ := by
      intro hP
      have : (⟨coeffH1Mk (rhoW M h3M κ) z1, hz1U⟩ : ↥U) ∈ P := by rw [hP]; trivial
      change Ntw (coeffH1Mk (rhoW M h3M κ) z1) = 0 at this
      rw [hN1] at this
      exact hzr this
    have hTP : ∀ (i : ι) (w : ↥U), TU i w - σ i.1 • w ∈ P := by
      intro i w
      change Ntw (Tgood S₀ hc i.1 i.2 (w : coeffH1 (rhoW M h3M κ)) - σ i.1 • (w : coeffH1 (rhoW M h3M κ))) = 0
      exact (hmemU _).mp w.2 i
    haveI : FiniteDimensional κ (coeffH1 (rhoW M h3M κ)) := finiteDimensional_coeffH1 M (rhoW M h3M κ)
    obtain ⟨v, hv, hTv⟩ := exists_common_eigenvector TU hTU (fun i => σ i.1) P hP hTP
    refine (isEigensystemH1_iff S₀ hc σ).mpr ⟨(v : coeffH1 (rhoW M h3M κ)), fun h0 => hv (Subtype.ext h0), fun ℓ hg => ?_⟩
    exact congrArg Subtype.val (hTv ⟨ℓ, hg⟩)

end Main

end QuadTwist3
p2m_reactivate "P2MW.S_HeckeEis_exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd.QuadTwist3"

open scoped MatrixGroups in
theorem solution
    (M : ℕ) [NeZero M] (h3M : 3 ∣ M) (S₀ : Set ℕ) (κ : Type) [Field κ] [CharP κ 3] (nu : ℕ → κ)
    (hocc : HeckeEis.IsEigensystemH1 M (1 : Representation κ (CongruenceSubgroup.Gamma0 M) κ)
      (fun _ => LinearMap.id) S₀ nu) :
    ∃ M' : ℕ, M ∣ M' ∧ M' ∣ M * 3 ∧
      HeckeEis.IsEigensystemH1 M' (1 : Representation κ (CongruenceSubgroup.Gamma0 M') κ)
        (fun _ => LinearMap.id) (insert 3 S₀) (fun ℓ => (ℓ : κ) * nu ℓ) :=
  QuadTwist3.main M h3M S₀ κ nu hocc

end S_HeckeEis_exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd
end P2MW
export P2MW.S_HeckeEis_exists_isEigensystemH1_one_natCast_mul_of_isEigensystemH1_one_of_three_dvd (solution)
