-- Prove2me | solution 1 for HeckeEis.exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/1c80970d-94dc-5e73-b9fc-ff723ae2c79d

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_HeckeEis_BinaryFormRep
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj
import Theorems.Thm_HeckeEis_coeffHeckeFun_coeffHeckeFun_sub_coeffHeckeFun_mul_mem_coeffCoboundaries
import Theorems.Thm_HeckeEis_exists_filtration_binaryForm_subquotient_le_sub_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1

set_option autoImplicit false

namespace R2WT

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

section Twist

variable {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]
variable (N : ℕ) (ρ : Representation K (Gamma0 N) V)

theorem coeffHeckeFun_smul (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V) (z : Gamma0 N → V) :
    coeffHeckeFun N ℓ ρ (c • a) z = c • coeffHeckeFun N ℓ ρ a z := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  ext g
  simp only [coeffHeckeFun_apply, Pi.smul_apply, LinearMap.smul_apply, map_smul, Finset.smul_sum]

theorem smul_isCoeffHeckeOnH1 (ℓ : ℕ) [NeZero ℓ] (c : K) (a : V →ₗ[K] V)
    {T : coeffH1 ρ →ₗ[K] coeffH1 ρ} (hT : IsCoeffHeckeOnH1 N ℓ ρ a T) :
    IsCoeffHeckeOnH1 N ℓ ρ (c • a) (c • T) := by
  intro z
  obtain ⟨w, hw, hTw⟩ := hT z
  refine ⟨c • w, ?_, ?_⟩
  · rw [Submodule.coe_smul, hw, coeffHeckeFun_smul]
  · rw [LinearMap.smul_apply, hTw, map_smul]

theorem isEigensystemH1_of_smul (a a' : ℕ → (V →ₗ[K] V)) (χ : ℕ → K) (S₀ : Set ℕ) (lam : ℕ → K)
    (haa' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a' ℓ = χ ℓ • a ℓ)
    (h : IsEigensystemH1 N ρ a S₀ lam) :
    IsEigensystemH1 N ρ a' S₀ (fun ℓ => χ ℓ * lam ℓ) := by
  obtain ⟨x, hx, heig⟩ := h
  refine ⟨x, hx, fun ℓ hℓ hℓN hℓS => ?_⟩
  obtain ⟨T, hT, hTx⟩ := heig ℓ hℓ hℓN hℓS
  haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
  refine ⟨χ ℓ • T, ?_, ?_⟩
  · have := smul_isCoeffHeckeOnH1 N ρ ℓ (χ ℓ) (a ℓ) hT
    rw [← haa' ℓ hℓ hℓN hℓS] at this
    exact this
  · rw [LinearMap.smul_apply, hTx, smul_smul]

theorem isEigensystemH1_of_smul_of_mul_eq_one (a a' : ℕ → (V →ₗ[K] V)) (χ χ' : ℕ → K) (S₀ : Set ℕ)
    (lam : ℕ → K) (haa' : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → a' ℓ = χ ℓ • a ℓ)
    (hunit : ∀ ℓ : ℕ, ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → χ' ℓ * χ ℓ = 1)
    (h : IsEigensystemH1 N ρ a' S₀ lam) :
    IsEigensystemH1 N ρ a S₀ (fun ℓ => χ' ℓ * lam ℓ) :=
  isEigensystemH1_of_smul N ρ a' a χ' S₀ lam
    (fun ℓ hℓ hℓN hℓS => by rw [haa' ℓ hℓ hℓN hℓS, smul_smul, hunit ℓ hℓ hℓN hℓS, one_smul]) h

end Twist

section Functorial

variable {K : Type*} [CommRing K]
variable {V W : Type*} [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable (N : ℕ) (ρV : Representation K (Gamma0 N) V) (ρW : Representation K (Gamma0 N) W)
variable (f : V →ₗ[K] W) (hf : ∀ g : Gamma0 N, f ∘ₗ ρV g = ρW g ∘ₗ f)

include hf in
theorem f_ρ (g : Gamma0 N) (v : V) : f (ρV g v) = ρW g (f v) :=
  LinearMap.congr_fun (hf g) v

include hf in
theorem comp_mem_coeffCocycles {z : Gamma0 N → V} (hz : z ∈ coeffCocycles ρV) :
    (f ∘ z) ∈ coeffCocycles ρW := by
  intro g h
  simp only [Function.comp_apply, hz g h, map_add, f_ρ N ρV ρW f hf]

def Z1map : ↥(coeffCocycles ρV) →ₗ[K] ↥(coeffCocycles ρW) where
  toFun z := ⟨f ∘ (z : Gamma0 N → V), comp_mem_coeffCocycles N ρV ρW f hf z.2⟩
  map_add' z w := by ext g; simp
  map_smul' c z := by ext g; simp

@[scoped simp] theorem coe_Z1map (z : ↥(coeffCocycles ρV)) :
    (Z1map N ρV ρW f hf z : Gamma0 N → W) = f ∘ (z : Gamma0 N → V) := rfl

theorem comap_le_comap_Z1map :
    (coeffCoboundaries ρV).comap (coeffCocycles ρV).subtype ≤
      ((coeffCoboundaries ρW).comap (coeffCocycles ρW).subtype).comap (Z1map N ρV ρW f hf) := by
  intro z hz
  obtain ⟨v, hv⟩ := (mem_coeffCoboundaries_iff ρV _).mp hz
  change f ∘ (z : Gamma0 N → V) ∈ coeffCoboundaries ρW
  refine (mem_coeffCoboundaries_iff ρW _).mpr ⟨f v, ?_⟩
  ext g
  have hvg := congrFun hv g
  change ρV g v - v = (z : Gamma0 N → V) g at hvg
  change ρW g (f v) - f v = f ((z : Gamma0 N → V) g)
  rw [← hvg, map_sub, f_ρ N ρV ρW f hf]

def H1map : coeffH1 ρV →ₗ[K] coeffH1 ρW :=
  ((coeffCoboundaries ρV).comap (coeffCocycles ρV).subtype).mapQ
    ((coeffCoboundaries ρW).comap (coeffCocycles ρW).subtype) (Z1map N ρV ρW f hf)
    (comap_le_comap_Z1map N ρV ρW f hf)

theorem H1map_mk (z : ↥(coeffCocycles ρV)) :
    H1map N ρV ρW f hf (coeffH1Mk ρV z) = coeffH1Mk ρW (Z1map N ρV ρW f hf z) := rfl

variable (aV : V →ₗ[K] V) (aW : W →ₗ[K] W) (hfa : f ∘ₗ aV = aW ∘ₗ f)

include hf hfa in

theorem comp_coeffHeckeFun (ℓ : ℕ) [NeZero ℓ] (z : Gamma0 N → V) :
    f ∘ coeffHeckeFun N ℓ ρV aV z = coeffHeckeFun N ℓ ρW aW (f ∘ z) := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  ext g
  simp only [Function.comp_apply, coeffHeckeFun_apply, map_sum, f_ρ N ρV ρW f hf]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  exact LinearMap.congr_fun hfa _

include hfa in

theorem H1map_heckeH1 (ℓ : ℕ) [NeZero ℓ] (haV : IsCompat N ℓ ρV aV) (haW : IsCompat N ℓ ρW aW)
    (x : coeffH1 ρV) :
    H1map N ρV ρW f hf (heckeH1 haV x) = heckeH1 haW (H1map N ρV ρW f hf x) := by
  obtain ⟨z, rfl⟩ := coeffH1Mk_surjective ρV x
  rw [heckeH1_mk, H1map_mk, H1map_mk, heckeH1_mk]
  congr 1
  refine Subtype.ext ?_
  rw [coe_Z1map, coe_heckeZ1, coe_heckeZ1, coe_Z1map, comp_coeffHeckeFun N ρV ρW f hf aV aW hfa]

end Functorial

section Exact

variable {K : Type*} [CommRing K]
variable {V' V V'' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup V] [Module K V]
  [AddCommGroup V''] [Module K V'']
variable (N : ℕ) (ρ' : Representation K (Gamma0 N) V') (ρ : Representation K (Gamma0 N) V)
  (ρ'' : Representation K (Gamma0 N) V'')
variable (i : V' →ₗ[K] V) (hi : ∀ g : Gamma0 N, i ∘ₗ ρ' g = ρ g ∘ₗ i)
variable (π : V →ₗ[K] V'') (hπ : ∀ g : Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)

include hi hπ in

theorem exists_H1map_eq_of_H1map_eq_zero (hinj : Function.Injective i)
    (hexact : LinearMap.range i = LinearMap.ker π) (hsurj : Function.Surjective π) (x : coeffH1 ρ)
    (hx : H1map N ρ ρ'' π hπ x = 0) :
    ∃ y : coeffH1 ρ', H1map N ρ' ρ i hi y = x := by
  obtain ⟨c, rfl⟩ := coeffH1Mk_surjective ρ x
  rw [H1map_mk, coeffH1Mk_eq_zero_iff] at hx
  change (π ∘ (c : Gamma0 N → V)) ∈ coeffCoboundaries ρ'' at hx
  obtain ⟨w'', hw''⟩ := (mem_coeffCoboundaries_iff ρ'' _).mp hx
  obtain ⟨w, rfl⟩ := hsurj w''
  have hval : ∀ g : Gamma0 N, (c : Gamma0 N → V) g - coeffCoboundaryMap ρ w g ∈ LinearMap.range i := by
    intro g
    rw [hexact, LinearMap.mem_ker, map_sub]
    have h1 := congrFun hw'' g
    simp only [Function.comp_apply] at h1
    rw [← h1, coeffCoboundaryMap_apply, map_sub, f_ρ N ρ ρ'' π hπ, sub_self]
  choose d hd using hval
  have hdc : (fun g => i (d g)) = (c : Gamma0 N → V) - coeffCoboundaryMap ρ w := funext hd
  have hd_mem : d ∈ coeffCocycles ρ' := by
    intro g h
    apply hinj
    rw [map_add, f_ρ N ρ' ρ i hi, hd, hd, hd]
    have hc2 := (c.2 : (c : Gamma0 N → V) ∈ coeffCocycles ρ) g h
    have hb2 := coeffCoboundaries_le_coeffCocycles ρ (LinearMap.mem_range_self _ w) g h
    simp only [hc2, hb2, map_sub, coeffCoboundaryMap_apply]
    abel
  refine ⟨coeffH1Mk ρ' ⟨d, hd_mem⟩, ?_⟩
  rw [H1map_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  change ((fun g => i (d g)) - (c : Gamma0 N → V)) ∈ coeffCoboundaries ρ
  rw [hdc, sub_sub_cancel_left]
  exact (coeffCoboundaries ρ).neg_mem (LinearMap.mem_range_self _ _)

end Exact

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
  push_neg at hz
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
      push_neg at h
      exact hP (Submodule.eq_top_iff'.mpr h)
    obtain ⟨v, hv⟩ := hex
    have hv0 : v ≠ 0 := fun h => hv (h ▸ P.zero_mem)
    haveI : Nontrivial M := nontrivial_of_ne v 0 hv0
    exact exists_common_ker_of_nilpotent d T hT hall inferInstance hd
  push_neg at hall
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

section Transport

variable {W : Type*} [AddCommGroup W] [Module K W]
variable {ρV : Representation K (Gamma0 N) V} {aV : ℕ → (V →ₗ[K] V)} (hcV : GoodCompat S₀ ρV aV)
variable {ρW : Representation K (Gamma0 N) W} {aW : ℕ → (W →ₗ[K] W)} (hcW : GoodCompat S₀ ρW aW)
variable (f : V →ₗ[K] W) (hf : ∀ g : Gamma0 N, f ∘ₗ ρV g = ρW g ∘ₗ f)
  (hfa : ∀ ℓ, Good N S₀ ℓ → f ∘ₗ aV ℓ = aW ℓ ∘ₗ f)

include hfa in
theorem H1map_Tgood (ℓ : ℕ) (h : Good N S₀ ℓ) (x : coeffH1 ρV) :
    H1map N ρV ρW f hf (Tgood S₀ hcV ℓ h x) = Tgood S₀ hcW ℓ h (H1map N ρV ρW f hf x) := by
  haveI := h.neZero
  exact H1map_heckeH1 N ρV ρW f hf (aV ℓ) (aW ℓ) (hfa ℓ h) ℓ (hcV ℓ h) (hcW ℓ h) x

include hfa in
theorem isEigvec_H1map {lam : ℕ → K} {x : coeffH1 ρV} (hx : IsEigvec S₀ hcV lam x) :
    IsEigvec S₀ hcW lam (H1map N ρV ρW f hf x) := by
  intro ℓ h
  rw [← H1map_Tgood S₀ hcV hcW f hf hfa ℓ h, hx ℓ h, map_smul]

end Transport

section Step

variable {V' V'' : Type*} [AddCommGroup V'] [Module K V'] [AddCommGroup V''] [Module K V'']
variable {ρ' : Representation K (Gamma0 N) V'} {a' : ℕ → (V' →ₗ[K] V')} (hc' : GoodCompat S₀ ρ' a')
variable {ρ : Representation K (Gamma0 N) V} {a : ℕ → (V →ₗ[K] V)} (hc : GoodCompat S₀ ρ a)
variable {ρ'' : Representation K (Gamma0 N) V''} {a'' : ℕ → (V'' →ₗ[K] V'')} (hc'' : GoodCompat S₀ ρ'' a'')
variable (i : V' →ₗ[K] V) (hi : ∀ g : Gamma0 N, i ∘ₗ ρ' g = ρ g ∘ₗ i)
  (hia : ∀ ℓ, Good N S₀ ℓ → i ∘ₗ a' ℓ = a ℓ ∘ₗ i)
variable (π : V →ₗ[K] V'') (hπ : ∀ g : Gamma0 N, π ∘ₗ ρ g = ρ'' g ∘ₗ π)
  (hπa : ∀ ℓ, Good N S₀ ℓ → π ∘ₗ a ℓ = a'' ℓ ∘ₗ π)

include hi hia hπ hπa in

theorem step [FiniteDimensional K (coeffH1 ρ')] (hcomm' : GoodCommute S₀ hc')
    (hinj : Function.Injective i) (hexact : LinearMap.range i = LinearMap.ker π)
    (hsurj : Function.Surjective π) (lam : ℕ → K) (x : coeffH1 ρ) (hx : x ≠ 0)
    (heig : IsEigvec S₀ hc lam x) :
    (∃ y : coeffH1 ρ'', y ≠ 0 ∧ IsEigvec S₀ hc'' lam y) ∨
      (∃ y : coeffH1 ρ', y ≠ 0 ∧ IsEigvec S₀ hc' lam y) := by
  by_cases hzero : H1map N ρ ρ'' π hπ x = 0
  swap
  · exact Or.inl ⟨_, hzero, isEigvec_H1map S₀ hc hc'' π hπ hπa heig⟩
  right
  obtain ⟨y₀, hy₀⟩ := exists_H1map_eq_of_H1map_eq_zero N ρ' ρ ρ'' i hi π hπ hinj hexact hsurj x hzero

  let M : Submodule K (coeffH1 ρ') := (Submodule.span K {x}).comap (H1map N ρ' ρ i hi)
  have hfx : ∀ m ∈ M, ∃ r : K, r • x = H1map N ρ' ρ i hi m := fun m hm =>
    Submodule.mem_span_singleton.mp hm
  have hstabM : ∀ ℓ (h : Good N S₀ ℓ), ∀ m ∈ M, Tgood S₀ hc' ℓ h m ∈ M := by
    intro ℓ h m hm
    obtain ⟨r, hr⟩ := hfx m hm
    change H1map N ρ' ρ i hi (Tgood S₀ hc' ℓ h m) ∈ Submodule.span K {x}
    rw [H1map_Tgood S₀ hc' hc i hi hia ℓ h, ← hr, map_smul, heig ℓ h, smul_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  let ι := {ℓ : ℕ // Good N S₀ ℓ}
  let TM : ι → ↥M →ₗ[K] ↥M := fun ℓ => (Tgood S₀ hc' ℓ.1 ℓ.2).restrict (hstabM ℓ.1 ℓ.2)
  have hTM : ∀ u v : ι, Commute (TM u) (TM v) := fun u v =>
    LinearMap.ext fun m => Subtype.ext (LinearMap.congr_fun (hcomm' u.1 v.1 u.2 v.2).eq (m : coeffH1 ρ'))
  let P : Submodule K ↥M := (LinearMap.ker (H1map N ρ' ρ i hi)).comap M.subtype
  have hy₀M : y₀ ∈ M := by
    change H1map N ρ' ρ i hi y₀ ∈ Submodule.span K {x}
    rw [hy₀]; exact Submodule.mem_span_singleton_self x
  have hP : P ≠ ⊤ := by
    intro h
    have : (⟨y₀, hy₀M⟩ : ↥M) ∈ P := by rw [h]; trivial
    change H1map N ρ' ρ i hi y₀ = 0 at this
    rw [hy₀] at this
    exact hx this
  have hTP : ∀ (u : ι) (m : ↥M), TM u m - lam u.1 • m ∈ P := by
    intro u m
    obtain ⟨r, hr⟩ := hfx m m.2
    change H1map N ρ' ρ i hi (Tgood S₀ hc' u.1 u.2 m - lam u.1 • (m : coeffH1 ρ')) = 0
    rw [map_sub, map_smul, H1map_Tgood S₀ hc' hc i hi hia u.1 u.2, ← hr, map_smul, heig u.1 u.2,
      smul_smul, smul_smul, mul_comm, sub_self]
  obtain ⟨v, hv, hTv⟩ := exists_common_eigenvector TM hTM (fun u => lam u.1) P hP hTP
  refine ⟨(v : coeffH1 ρ'), fun h => hv (Subtype.ext h), fun ℓ h => ?_⟩
  exact congrArg Subtype.val (hTv ⟨ℓ, h⟩)

end Step

section Sub

variable (ρ : Representation K (Gamma0 N) V) (a : ℕ → (V →ₗ[K] V))
variable (W : Submodule K V) (hρW : ∀ g : Gamma0 N, ∀ v ∈ W, ρ g v ∈ W)
  (haW : ∀ ℓ, Good N S₀ ℓ → ∀ v ∈ W, a ℓ v ∈ W)

def subRep : Representation K (Gamma0 N) ↥W where
  toFun g := (ρ g).restrict (hρW g)
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by simp)

@[scoped simp] theorem coe_subRep_apply (g : Gamma0 N) (v : ↥W) :
    ((subRep ρ W hρW g v : ↥W) : V) = ρ g v := rfl

open Classical in

noncomputable def subFam : ℕ → (↥W →ₗ[K] ↥W) := fun ℓ =>
  if h : Good N S₀ ℓ then (a ℓ).restrict (haW ℓ h) else 0

theorem subFam_of_good {ℓ : ℕ} (h : Good N S₀ ℓ) :
    subFam S₀ a W haW ℓ = (a ℓ).restrict (haW ℓ h) := by
  simp [subFam, h]

@[scoped simp] theorem coe_subFam_apply {ℓ : ℕ} (h : Good N S₀ ℓ) (v : ↥W) :
    ((subFam S₀ a W haW ℓ v : ↥W) : V) = a ℓ v := by
  rw [subFam_of_good S₀ a W haW h]; rfl

theorem goodCompat_sub (hc : GoodCompat S₀ ρ a) : GoodCompat S₀ (subRep ρ W hρW) (subFam S₀ a W haW) := by
  intro ℓ h u
  refine LinearMap.ext fun v => Subtype.ext ?_
  change ((subFam S₀ a W haW ℓ (subRep ρ W hρW _ v) : ↥W) : V) =
    ((subRep ρ W hρW _ (subFam S₀ a W haW ℓ v) : ↥W) : V)
  rw [coe_subFam_apply S₀ a W haW h, coe_subRep_apply, coe_subRep_apply, coe_subFam_apply S₀ a W haW h]
  exact LinearMap.congr_fun (hc ℓ h u) (v : V)

theorem sub_comm (hcomm : ∀ ℓ ℓ', Good N S₀ ℓ → Good N S₀ ℓ' → a ℓ ∘ₗ a ℓ' = a ℓ' ∘ₗ a ℓ)
    (ℓ ℓ' : ℕ) (h : Good N S₀ ℓ) (h' : Good N S₀ ℓ') :
    subFam S₀ a W haW ℓ ∘ₗ subFam S₀ a W haW ℓ' = subFam S₀ a W haW ℓ' ∘ₗ subFam S₀ a W haW ℓ := by
  refine LinearMap.ext fun v => Subtype.ext ?_
  change ((subFam S₀ a W haW ℓ (subFam S₀ a W haW ℓ' v) : ↥W) : V) =
    ((subFam S₀ a W haW ℓ' (subFam S₀ a W haW ℓ v) : ↥W) : V)
  rw [coe_subFam_apply S₀ a W haW h, coe_subFam_apply S₀ a W haW h', coe_subFam_apply S₀ a W haW h',
    coe_subFam_apply S₀ a W haW h]
  exact LinearMap.congr_fun (hcomm ℓ ℓ' h h') (v : V)

end Sub

end Systems

section Tower

variable (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [CharP F p] (N : ℕ) [NeZero N] (S₀ : Set ℕ)

theorem natCast_pow_sub_one_eq_one {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓp : ℓ ≠ p) : (ℓ : F) ^ (p - 1) = 1 := by
  have hne : (ℓ : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    exact hℓp ((Nat.prime_dvd_prime_iff_eq (Fact.out) hℓ).mp h).symm
  have h := ZMod.pow_card_sub_one_eq_one hne
  have := congrArg (ZMod.castHom (dvd_refl p) F) h
  rwa [map_pow, map_natCast, map_one] at this

def dMat (ℓ : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![(ℓ : ℤ), 0; 0, 1]

theorem det_dMat (ℓ : ℕ) : (dMat ℓ).det = (ℓ : ℤ) := by
  rw [dMat, Matrix.det_fin_two_of]; ring

theorem dMat_comm (ℓ ℓ' : ℕ) : dMat ℓ * dMat ℓ' = dMat ℓ' * dMat ℓ := by
  simp only [dMat, Matrix.mul_fin_two]
  congr 1 <;> ring

theorem binaryFormAlphaAdj_eq (n ℓ : ℕ) : binaryFormAlphaAdj F n ℓ = binaryFormRep F n (dMat ℓ) := rfl

variable {p S₀} in
theorem not_dvd_det_dMat_of_good (hS₀p : p ∈ S₀) {ℓ : ℕ} (h : Good N S₀ ℓ) : ¬ (p : ℤ) ∣ (dMat ℓ).det := by
  rw [det_dMat]
  intro hd
  have hd' : p ∣ ℓ := by exact_mod_cast hd
  have : p = ℓ := (Nat.prime_dvd_prime_iff_eq (Fact.out) h.1).mp hd'
  exact h.2.2 (this ▸ hS₀p)

theorem not_dvd_det_gamma (γ : Gamma0 N) :
    ¬ (p : ℤ) ∣ (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)).det := by
  rw [(γ : SL(2, ℤ)).2]
  intro hd
  have : p ∣ 1 := by exact_mod_cast hd
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)

variable (n : ℕ)

noncomputable abbrev ρSym : Representation F (Gamma0 N) ↥(BinaryForm F n) :=
  (binaryFormRepSL F n).comp (Gamma0 N).subtype

theorem ρSym_apply (γ : Gamma0 N) :
    ρSym F N n γ = binaryFormRep F n (((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)) := rfl

theorem isCompat_sym (ℓ : ℕ) [NeZero ℓ] : IsCompat N ℓ (ρSym F N n) (binaryFormAlphaAdj F n ℓ) :=
  fun u => binaryFormAlphaAdj_comp_binaryFormRepSL_heckeConj F n N ℓ u

theorem goodCompat_sym_smul (c : ℕ → F) :
    GoodCompat S₀ (ρSym F N n) (fun ℓ => c ℓ • binaryFormAlphaAdj F n ℓ) := by
  intro ℓ h u
  haveI := h.neZero
  rw [LinearMap.smul_comp, LinearMap.comp_smul, isCompat_sym F N n ℓ u]

theorem goodCompat_sym : GoodCompat S₀ (ρSym F N n) (fun ℓ => binaryFormAlphaAdj F n ℓ) := by
  intro ℓ h u
  haveI := h.neZero
  exact isCompat_sym F N n ℓ u

theorem alpha_comm (ℓ ℓ' : ℕ) :
    binaryFormAlphaAdj F n ℓ ∘ₗ binaryFormAlphaAdj F n ℓ' = binaryFormAlphaAdj F n ℓ' ∘ₗ binaryFormAlphaAdj F n ℓ := by
  rw [binaryFormAlphaAdj_eq, binaryFormAlphaAdj_eq]
  change binaryFormRep F n (dMat ℓ) * binaryFormRep F n (dMat ℓ') =
    binaryFormRep F n (dMat ℓ') * binaryFormRep F n (dMat ℓ)
  rw [← map_mul, ← map_mul, dMat_comm]

scoped instance finiteDimensional_binaryForm : FiniteDimensional F ↥(BinaryForm F n) := by
  have hle : BinaryForm F n ≤ MvPolynomial.restrictTotalDegree (Fin 2) F n := fun φ hφ =>
    (MvPolynomial.mem_restrictTotalDegree _ _ _).mpr
      ((MvPolynomial.mem_homogeneousSubmodule n φ).mp hφ).totalDegree_le
  exact Submodule.finiteDimensional_of_le hle

variable {n}
variable {r : ℕ} (W : Fin (r + 1) → Submodule F ↥(BinaryForm F n))
  (hstab : ∀ (i : Fin (r + 1)) (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det →
    Submodule.map (binaryFormRep F n M) (W i) ≤ W i)
  (hS₀p : p ∈ S₀)

include hstab in
theorem stab_gamma (i : Fin (r + 1)) (g : Gamma0 N) (v : ↥(BinaryForm F n)) (hv : v ∈ W i) :
    ρSym F N n g v ∈ W i :=
  hstab i _ (not_dvd_det_gamma p N g) ⟨v, hv, rfl⟩

include hstab hS₀p in
theorem stab_alpha (i : Fin (r + 1)) (ℓ : ℕ) (h : Good N S₀ ℓ) (v : ↥(BinaryForm F n)) (hv : v ∈ W i) :
    binaryFormAlphaAdj F n ℓ v ∈ W i :=
  hstab i _ (not_dvd_det_dMat_of_good N hS₀p h) ⟨v, hv, rfl⟩

noncomputable def ρW (i : Fin (r + 1)) : Representation F (Gamma0 N) ↥(W i) :=
  subRep (ρSym F N n) (W i) (fun g v hv => stab_gamma p F N W hstab i g v hv)

noncomputable def aW (i : Fin (r + 1)) : ℕ → (↥(W i) →ₗ[F] ↥(W i)) :=
  subFam S₀ (fun ℓ => binaryFormAlphaAdj F n ℓ) (W i)
    (fun ℓ h v hv => stab_alpha p F N S₀ W hstab hS₀p i ℓ h v hv)

theorem goodCompat_W (i : Fin (r + 1)) :
    GoodCompat (V := ↥(W i)) S₀ (ρW p F N W hstab i) (aW p F N S₀ W hstab hS₀p i) :=
  goodCompat_sub S₀ _ _ (W i) _ _ (goodCompat_sym F N S₀ n)

theorem goodCommute_W (i : Fin (r + 1)) : GoodCommute S₀ (goodCompat_W p F N S₀ W hstab hS₀p i) :=
  goodCommute_of_comm S₀ _ (sub_comm S₀ _ (W i) _ (fun ℓ ℓ' _ _ => alpha_comm F n ℓ ℓ'))

abbrev H1W (i : Fin (r + 1)) : Type := coeffH1 (V := ↥(W i)) (ρW p F N W hstab i)

scoped instance finiteDimensional_coeffH1_W (i : Fin (r + 1)) : FiniteDimensional F (H1W p F N W hstab i) :=
  finiteDimensional_coeffH1 (V := ↥(W i)) N _

def Goal (lam : ℕ → F) : Prop :=
  ∃ a : ℕ, a ≤ p - 1 ∧ ∃ j : ℕ, IsEigensystemH1 N (ρSym F N a)
    (fun ℓ => binaryFormAlphaAdj F a ℓ) S₀ (fun ℓ => (ℓ : F) ^ j * lam ℓ)

include hS₀p in

theorem goal_of_twisted (lam : ℕ → F) (a b : ℕ) (ha : a ≤ p - 1) (y : coeffH1 (ρSym F N a)) (hy : y ≠ 0)
    (heig : IsEigvec S₀ (goodCompat_sym_smul F N S₀ a (fun ℓ => (ℓ : F) ^ b)) lam y) :
    Goal p F N S₀ lam := by
  refine ⟨a, ha, b * (p - 2), ?_⟩
  have h1 : IsEigensystemH1 N (ρSym F N a) (fun ℓ => ((ℓ : F) ^ b) • binaryFormAlphaAdj F a ℓ) S₀ lam :=
    (isEigensystemH1_iff S₀ (goodCompat_sym_smul F N S₀ a (fun ℓ => (ℓ : F) ^ b)) lam).mpr ⟨y, hy, heig⟩
  refine isEigensystemH1_of_smul_of_mul_eq_one N (ρSym F N a) (fun ℓ => binaryFormAlphaAdj F a ℓ)
    (fun ℓ => ((ℓ : F) ^ b) • binaryFormAlphaAdj F a ℓ) (fun ℓ => (ℓ : F) ^ b)
    (fun ℓ => (ℓ : F) ^ (b * (p - 2))) S₀ lam (fun ℓ _ _ _ => rfl) ?_ h1
  intro ℓ hℓ _ hℓS
  have hℓp : ℓ ≠ p := fun h => hℓS (h ▸ hS₀p)
  show (ℓ : F) ^ (b * (p - 2)) * (ℓ : F) ^ b = 1
  have h2 : b * (p - 2) + b = b * (p - 1) := by
    rw [show p - 1 = (p - 2) + 1 by have := (Fact.out : p.Prime).two_le; omega]
    ring
  rw [← pow_add, h2, pow_mul', natCast_pow_sub_one_eq_one p F hℓ hℓp, one_pow]

variable (hstep : ∀ i : Fin r, ∃ (a b : ℕ) (π : ↥(BinaryForm F n) →ₗ[F] ↥(BinaryForm F a)),
    a ≤ p - 1 ∧ Submodule.map π (W i.succ) = ⊤ ∧ W i.castSucc = W i.succ ⊓ LinearMap.ker π ∧
    ∀ (M : Matrix (Fin 2) (Fin 2) ℤ), ¬ (p : ℤ) ∣ M.det → ∀ w ∈ W i.succ,
      π (binaryFormRep F n M w) = (((M.det : ℤ) : F) ^ b) • binaryFormRep F a M (π w))
  (hW0 : W 0 = ⊥)

include hstep hW0 in

theorem descend (lam : ℕ → F) : ∀ (k : ℕ) (hk : k < r + 1),
    (∃ x : H1W p F N W hstab ⟨k, hk⟩, x ≠ 0 ∧
      IsEigvec S₀ (goodCompat_W p F N S₀ W hstab hS₀p ⟨k, hk⟩) lam x) → Goal p F N S₀ lam := by
  intro k
  induction k with
  | zero =>
    rintro hk ⟨x, hx, -⟩
    exfalso
    apply hx
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
    have hz : z = 0 := by
      refine Subtype.ext (funext fun g => ?_)
      have hmem : (((z : Gamma0 N → ↥(W ⟨0, hk⟩)) g : ↥(W ⟨0, hk⟩)) : ↥(BinaryForm F n)) ∈ W 0 :=
        ((z : Gamma0 N → ↥(W ⟨0, hk⟩)) g).2
      rw [hW0, Submodule.mem_bot] at hmem
      exact Subtype.ext hmem
    rw [hz, map_zero]
  | succ k ih =>
    rintro hk ⟨x, hx, heig⟩
    have hk' : k < r + 1 := by omega
    let i : Fin r := ⟨k, by omega⟩
    obtain ⟨a, b, π, ha, hmapTop, hker, heqv⟩ := hstep i

    have hle : W ⟨k, hk'⟩ ≤ W ⟨k + 1, hk⟩ := by
      change W i.castSucc ≤ W i.succ
      rw [hker]; exact inf_le_left
    let incl : ↥(W ⟨k, hk'⟩) →ₗ[F] ↥(W ⟨k + 1, hk⟩) := Submodule.inclusion hle
    let πk : ↥(W ⟨k + 1, hk⟩) →ₗ[F] ↥(BinaryForm F a) := π ∘ₗ (W ⟨k + 1, hk⟩).subtype
    have hincl : ∀ g : Gamma0 N,
        incl ∘ₗ ρW p F N W hstab ⟨k, hk'⟩ g = ρW p F N W hstab ⟨k + 1, hk⟩ g ∘ₗ incl :=
      fun g => LinearMap.ext fun v => Subtype.ext rfl
    have hincla : ∀ ℓ, Good N S₀ ℓ →
        incl ∘ₗ aW p F N S₀ W hstab hS₀p ⟨k, hk'⟩ ℓ = aW p F N S₀ W hstab hS₀p ⟨k + 1, hk⟩ ℓ ∘ₗ incl := by
      intro ℓ h
      refine LinearMap.ext fun v => Subtype.ext ?_
      change (((aW p F N S₀ W hstab hS₀p ⟨k, hk'⟩ ℓ v) : ↥(W ⟨k, hk'⟩)) : ↥(BinaryForm F n)) =
        ((aW p F N S₀ W hstab hS₀p ⟨k + 1, hk⟩ ℓ (incl v) : ↥(W ⟨k + 1, hk⟩)) : ↥(BinaryForm F n))
      rw [aW, aW, coe_subFam_apply S₀ _ _ _ h, coe_subFam_apply S₀ _ _ _ h]
      rfl
    have hπρ : ∀ g : Gamma0 N, πk ∘ₗ ρW p F N W hstab ⟨k + 1, hk⟩ g = ρSym F N a g ∘ₗ πk := by
      intro g
      refine LinearMap.ext fun v => ?_
      change π (ρSym F N n g (v : ↥(BinaryForm F n))) = ρSym F N a g (π v)
      rw [ρSym_apply, ρSym_apply, heqv _ (not_dvd_det_gamma p N g) _ v.2]
      have : ((((g : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).det : ℤ) : F) = 1 := by
        rw [(g : SL(2, ℤ)).2, Int.cast_one]
      rw [this, one_pow, one_smul]
    have hπa : ∀ ℓ, Good N S₀ ℓ →
        πk ∘ₗ aW p F N S₀ W hstab hS₀p ⟨k + 1, hk⟩ ℓ = (((ℓ : F) ^ b) • binaryFormAlphaAdj F a ℓ) ∘ₗ πk := by
      intro ℓ h
      refine LinearMap.ext fun v => ?_
      change π (((aW p F N S₀ W hstab hS₀p ⟨k + 1, hk⟩ ℓ v) : ↥(W ⟨k + 1, hk⟩)) : ↥(BinaryForm F n)) =
        ((ℓ : F) ^ b) • binaryFormAlphaAdj F a ℓ (π v)
      rw [aW, coe_subFam_apply S₀ _ _ _ h, binaryFormAlphaAdj_eq, binaryFormAlphaAdj_eq,
        heqv _ (not_dvd_det_dMat_of_good N hS₀p h) _ v.2, det_dMat, Int.cast_natCast]
    have hinj : Function.Injective incl := Submodule.inclusion_injective hle
    have hexact : LinearMap.range incl = LinearMap.ker πk := by
      change LinearMap.range (Submodule.inclusion hle) = LinearMap.ker (π ∘ₗ (W ⟨k + 1, hk⟩).subtype)
      rw [Submodule.range_inclusion, LinearMap.ker_comp]
      change Submodule.comap (W i.succ).subtype (W i.castSucc) = Submodule.comap (W i.succ).subtype (LinearMap.ker π)
      rw [hker, Submodule.comap_inf, Submodule.comap_subtype_self, top_inf_eq]
    have hπsurj : Function.Surjective πk := by
      intro y
      have hy : y ∈ Submodule.map π (W i.succ) := by rw [hmapTop]; trivial
      obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.mp hy
      exact ⟨⟨w, hw⟩, hwy⟩
    have hres := step (V' := ↥(W ⟨k, hk'⟩)) (V := ↥(W ⟨k + 1, hk⟩)) (V'' := ↥(BinaryForm F a)) S₀
      (goodCompat_W p F N S₀ W hstab hS₀p ⟨k, hk'⟩) (goodCompat_W p F N S₀ W hstab hS₀p ⟨k + 1, hk⟩)
      (goodCompat_sym_smul F N S₀ a (fun ℓ => (ℓ : F) ^ b)) incl hincl hincla πk hπρ hπa
      (goodCommute_W p F N S₀ W hstab hS₀p ⟨k, hk'⟩) hinj hexact hπsurj lam x hx heig
    rcases hres with ⟨y, hy, hyeig⟩ | ⟨y, hy, hyeig⟩
    · exact goal_of_twisted p F N S₀ hS₀p lam a b ha y hy hyeig
    · exact ih hk' ⟨y, hy, hyeig⟩

theorem top (hWr : W (Fin.last r) = ⊤) (lam : ℕ → F) (x : coeffH1 (ρSym F N n)) (hx : x ≠ 0)
    (heig : IsEigvec S₀ (goodCompat_sym F N S₀ n) lam x) :
    ∃ y : H1W p F N W hstab (Fin.last r), y ≠ 0 ∧
      IsEigvec S₀ (goodCompat_W p F N S₀ W hstab hS₀p (Fin.last r)) lam y := by
  let e : ↥(BinaryForm F n) →ₗ[F] ↥(W (Fin.last r)) :=
    LinearMap.codRestrict (W (Fin.last r)) LinearMap.id (fun v => by rw [hWr]; trivial)
  have he : ∀ g : Gamma0 N, e ∘ₗ ρSym F N n g = ρW p F N W hstab (Fin.last r) g ∘ₗ e :=
    fun g => LinearMap.ext fun v => Subtype.ext rfl
  have hea : ∀ ℓ, Good N S₀ ℓ →
      e ∘ₗ binaryFormAlphaAdj F n ℓ = aW p F N S₀ W hstab hS₀p (Fin.last r) ℓ ∘ₗ e := by
    intro ℓ h
    refine LinearMap.ext fun v => Subtype.ext ?_
    change binaryFormAlphaAdj F n ℓ v =
      ((aW p F N S₀ W hstab hS₀p (Fin.last r) ℓ (e v) : ↥(W (Fin.last r))) : ↥(BinaryForm F n))
    rw [aW, coe_subFam_apply S₀ _ _ _ h]
    rfl
  have hsub : ∀ g : Gamma0 N,
      (W (Fin.last r)).subtype ∘ₗ ρW p F N W hstab (Fin.last r) g = ρSym F N n g ∘ₗ (W (Fin.last r)).subtype :=
    fun g => LinearMap.ext fun v => rfl
  refine ⟨H1map (V := ↥(BinaryForm F n)) (W := ↥(W (Fin.last r))) N (ρSym F N n)
      (ρW p F N W hstab (Fin.last r)) e he x, ?_,
    isEigvec_H1map (V := ↥(BinaryForm F n)) (W := ↥(W (Fin.last r))) S₀ (goodCompat_sym F N S₀ n)
      (goodCompat_W p F N S₀ W hstab hS₀p (Fin.last r)) e he hea heig⟩

  intro h0
  apply hx
  have hret : H1map (V := ↥(W (Fin.last r))) (W := ↥(BinaryForm F n)) N (ρW p F N W hstab (Fin.last r))
      (ρSym F N n) (W (Fin.last r)).subtype hsub
      (H1map (V := ↥(BinaryForm F n)) (W := ↥(W (Fin.last r))) N (ρSym F N n)
        (ρW p F N W hstab (Fin.last r)) e he x) = x := by
    obtain ⟨z, rfl⟩ := coeffH1Mk_surjective _ x
    rw [H1map_mk, H1map_mk]
    congr 1
  rw [← hret, h0, map_zero]

end Tower

end R2WT
p2m_reactivate "P2MW.S_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1.R2WT"

open scoped MatrixGroups in
theorem solution
    (p : ℕ) (hp : p.Prime) (N : ℕ) [NeZero N] (S₀ : Set ℕ) (hS₀p : p ∈ S₀)
    (F : Type) [Field F] [CharP F p] (n : ℕ) (lam : ℕ → F)
    (hocc : HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL F n).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F n ℓ) S₀ lam) :
    ∃ a : ℕ, a ≤ p - 1 ∧ ∃ j : ℕ, HeckeEis.IsEigensystemH1 N
      ((HeckeEis.binaryFormRepSL F a).comp (CongruenceSubgroup.Gamma0 N).subtype)
      (fun ℓ => HeckeEis.binaryFormAlphaAdj F a ℓ) S₀ (fun ℓ => (ℓ : F) ^ j * lam ℓ) := by
  open R2WT in
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨r, W, hW0, hWr, -, hstab, hstep⟩ :=
    HeckeEis.exists_filtration_binaryForm_subquotient_le_sub_one p F n
  obtain ⟨x, hx, heig⟩ := (isEigensystemH1_iff S₀ (goodCompat_sym F N S₀ n) lam).mp hocc
  obtain ⟨y, hy, hyeig⟩ := top p F N S₀ W hstab hS₀p hWr lam x hx heig
  exact descend p F N S₀ W hstab hS₀p hstep hW0 lam r (lt_add_one r) ⟨y, hy, hyeig⟩

end S_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1
end P2MW
export P2MW.S_HeckeEis_exists_le_sub_one_isEigensystemH1_binaryFormRepSL_of_isEigensystemH1 (solution)
