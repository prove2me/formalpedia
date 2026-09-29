-- Prove2me | solution 1 for IsLocalRing.exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/15b165f7-50cd-5e45-915d-802b26dc4ea4

import Mathlib
import Definitions.Def_AdicCompletionGaloisAction
import Definitions.Def_AdicCompletionLocalRing
import Theorems.Thm_Algebra_IsInvariant_isInvariant_adicCompletion_stabilizer_and_injective_and_finite
import Theorems.Thm_AdicCompletion_exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal
import Theorems.Thm_AdicCompletion_isNoetherianRing_and_exists_isLocalRing_maximalIdeal_eq_map_of_isMaximal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
p2m_attr_erase "simp" "AdicCompletion.tensorRingEquiv_tmul AdicCompletion.completionOfAlgHom_apply AdicCompletion.completionBaseChangeHom_of AdicCompletion.tensorRingHom_tmul"

set_option autoImplicit false
set_option maxHeartbeats 0
set_option synthInstance.maxHeartbeats 1600000

open IsLocalRing
open scoped Pointwise AdicCompletion.GaloisAction

namespace QuotLoc

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section PartA

variable (G : Subgroup (K ≃ₐ[k] K))
  (Õ : Subring K) [IsLocalRing ↥Õ]
  (O₀ : Subring K) (hO₀ : ∀ f : K, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)

include hO₀

theorem O₀_le : O₀ ≤ Õ := fun f hf => ((hO₀ f).mp hf).1

theorem isUnit_iff (f : ↥O₀) : IsUnit f ↔ IsUnit (Subring.inclusion (O₀_le G Õ O₀ hO₀) f) := by
  constructor
  · intro h; exact h.map _
  · intro h
    obtain ⟨u, hu⟩ := h
    set g : ↥Õ := ↑u⁻¹ with hg
    have hfg : (f : K) * (g : K) = 1 := by
      have := congrArg (fun z : ↥Õ => (z : K)) u.mul_inv
      rw [hu] at this
      simpa using this
    have hf0 : (f : K) ≠ 0 := fun h0 => by rw [h0, zero_mul] at hfg; exact zero_ne_one hfg
    have hgeq : (g : K) = (f : K)⁻¹ := by
      calc (g : K) = (f : K)⁻¹ * ((f : K) * (g : K)) := by rw [← mul_assoc, inv_mul_cancel₀ hf0, one_mul]
        _ = (f : K)⁻¹ := by rw [hfg, mul_one]
    have hginv : ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ (g : K) = (g : K) := by
      intro σ hσ
      rw [hgeq, map_inv₀, ((hO₀ f).mp f.2).2 σ hσ]
    have hgO₀ : (g : K) ∈ O₀ := (hO₀ _).mpr ⟨g.2, hginv⟩
    refine isUnit_iff_exists_inv.mpr ⟨⟨(g : K), hgO₀⟩, Subtype.ext ?_⟩
    simpa using hfg

theorem isLocalRing_O₀ : IsLocalRing ↥O₀ := by
  haveI : Nontrivial ↥O₀ := ⟨⟨0, 1, fun h => zero_ne_one (congrArg (fun z : ↥O₀ => (z : K)) h)⟩⟩
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (Subring.inclusion (O₀_le G Õ O₀ hO₀) a) with h | h
  · exact Or.inl ((isUnit_iff G Õ O₀ hO₀ a).mpr h)
  · right
    rw [isUnit_iff G Õ O₀ hO₀]
    simpa [map_sub] using h

end PartA

section Localisation

variable (B Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
  (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

include hBÕ

def ctr : Ideal ↥B := (maximalIdeal ↥Õ).comap (Subring.inclusion hBÕ)

scoped instance isPrime_ctr : (ctr B Õ hBÕ).IsPrime := Ideal.comap_isPrime _ _

theorem mem_ctr_iff (b : ↥B) : b ∈ ctr B Õ hBÕ ↔ ¬ IsUnit (⟨(b : K), hBÕ b.2⟩ : ↥Õ) := by
  rw [ctr, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; rfl

include hloc

theorem isLocalization_ctr :
    @IsLocalization ↥B _ (ctr B Õ hBÕ).primeCompl ↥Õ _ (Subring.inclusion hBÕ).toAlgebra := by
  letI : Algebra ↥B ↥Õ := (Subring.inclusion hBÕ).toAlgebra
  have halg : ∀ b : ↥B, algebraMap ↥B ↥Õ b = Subring.inclusion hBÕ b := fun _ => rfl
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · rintro ⟨s, hs⟩
    rw [halg]
    by_contra hu
    exact hs ((IsLocalRing.mem_maximalIdeal _).mpr hu)
  · intro f
    obtain ⟨g, h, hg, hh, hunit, e⟩ := (hloc f).mp f.2
    have hhu : IsUnit (⟨h, hBÕ hh⟩ : ↥Õ) := hunit (hBÕ hh)
    have hhq : (⟨h, hh⟩ : ↥B) ∉ ctr B Õ hBÕ := fun hm =>
      ((IsLocalRing.mem_maximalIdeal _).mp hm) hhu
    refine ⟨⟨⟨g, hg⟩, ⟨⟨h, hh⟩, hhq⟩⟩, Subtype.ext ?_⟩
    show (f : K) * h = g
    exact e
  · intro a b hab
    refine ⟨1, ?_⟩
    have h1 : (Subring.inclusion hBÕ a : K) = (Subring.inclusion hBÕ b : K) := congrArg (fun z : ↥Õ => (z : K)) hab
    have : (a : K) = (b : K) := h1
    rw [Subtype.ext this]

theorem isNoetherianRing_of_isLocalization [IsNoetherianRing ↥B] : IsNoetherianRing ↥Õ := by
  letI : Algebra ↥B ↥Õ := (Subring.inclusion hBÕ).toAlgebra
  haveI := isLocalization_ctr B Õ hBÕ hloc
  exact IsLocalization.isNoetherianRing (ctr B Õ hBÕ).primeCompl ↥Õ inferInstance

end Localisation

section PartB

variable (G : Subgroup (K ≃ₐ[k] K))
  (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
  (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
  (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

include hBG hBÕ hloc

theorem exists_invariant_fraction [Finite ↥G] (f : K) (hfÕ : f ∈ Õ) (hfG : ∀ σ : ↥G, σ • f = f) :
    ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ σ : ↥G, σ • g = g) ∧ (∀ σ : ↥G, σ • h = h) ∧
      (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g := by
  classical
  haveI : Fintype ↥G := Fintype.ofFinite ↥G
  have hBG' : ∀ (σ : ↥G) (b : K), b ∈ B → σ • b ∈ B := fun σ b hb => hBG σ σ.2 b hb

  let I : Ideal ↥B :=
    { carrier := {h | f * (h : K) ∈ B}
      add_mem' := fun {a b} ha hb => by
        change f * ((a : K) + b) ∈ B
        rw [mul_add]; exact B.add_mem ha hb
      zero_mem' := by change f * (0 : K) ∈ B; rw [mul_zero]; exact B.zero_mem
      smul_mem' := fun c {a} ha => by
        change f * ((c : K) * a) ∈ B
        rw [mul_left_comm]; exact B.mul_mem c.2 ha }
  have memI : ∀ h : ↥B, h ∈ I ↔ f * (h : K) ∈ B := fun _ => Iff.rfl

  let φ : ↥G → (↥B →+* ↥Õ) := fun σ =>
    { toFun := fun b => ⟨σ • (b : K), hBÕ (hBG' σ _ b.2)⟩
      map_one' := Subtype.ext (by change σ • ((1 : ↥B) : K) = 1; rw [OneMemClass.coe_one, smul_one])
      map_mul' := fun a b => Subtype.ext (by change σ • ((a : K) * b) = σ • (a : K) * σ • (b : K); rw [smul_mul'])
      map_zero' := Subtype.ext (by change σ • ((0 : ↥B) : K) = 0; rw [ZeroMemClass.coe_zero, smul_zero])
      map_add' := fun a b => Subtype.ext (by change σ • ((a : K) + b) = σ • (a : K) + σ • (b : K); rw [smul_add]) }
  let Q : ↥G → Ideal ↥B := fun σ => Ideal.comap (φ σ) (IsLocalRing.maximalIdeal ↥Õ)
  have hQprime : ∀ σ, (Q σ).IsPrime := fun σ => Ideal.comap_isPrime (φ σ) _
  have memQ : ∀ (σ : ↥G) (b : ↥B), b ∈ Q σ ↔ (⟨σ • (b : K), hBÕ (hBG' σ _ b.2)⟩ : ↥Õ) ∈ IsLocalRing.maximalIdeal ↥Õ :=
    fun _ _ => Iff.rfl

  obtain ⟨g₁, h₁, hg₁B, hh₁B, hh₁u, hfh₁⟩ := (hloc f).mp hfÕ
  have hnot : ∀ σ : ↥G, ¬ (I ≤ Q σ) := by
    intro σ hle
    have hmem : (⟨σ⁻¹ • h₁, hBG' _ _ hh₁B⟩ : ↥B) ∈ I := by
      rw [memI]
      change f * (σ⁻¹ • h₁) ∈ B
      have : f * (σ⁻¹ • h₁) = σ⁻¹ • (f * h₁) := by rw [smul_mul', hfG σ⁻¹]
      rw [this, hfh₁]; exact hBG' _ _ hg₁B
    have h2 := hle hmem
    rw [memQ] at h2
    apply (IsLocalRing.mem_maximalIdeal _).mp ?_ (hh₁u (hBÕ hh₁B))
    have e : (⟨σ • ((⟨σ⁻¹ • h₁, hBG' _ _ hh₁B⟩ : ↥B) : K), hBÕ (hBG' σ _ (hBG' _ _ hh₁B))⟩ : ↥Õ) = ⟨h₁, hBÕ hh₁B⟩ := by
      apply Subtype.ext; change σ • σ⁻¹ • h₁ = h₁; rw [smul_inv_smul]
    rw [← e]; exact h2

  have havoid : ¬ ((I : Set ↥B) ⊆ ⋃ σ ∈ (↑(Finset.univ : Finset ↥G) : Set ↥G), ((Q σ) : Set ↥B)) := by
    rw [Ideal.subset_union_prime (1 : ↥G) (1 : ↥G) (fun σ _ _ _ => hQprime σ)]
    rintro ⟨σ, -, hle⟩
    exact hnot σ hle
  rw [Set.not_subset] at havoid
  obtain ⟨h, hhI, hhQ⟩ := havoid
  have hhQ' : ∀ σ : ↥G, h ∉ Q σ := by
    intro σ hσ
    apply hhQ
    rw [Set.mem_iUnion₂]
    exact ⟨σ, Finset.mem_coe.mpr (Finset.mem_univ σ), hσ⟩
  have hfhB : f * (h : K) ∈ B := (memI h).mp hhI

  have hσhB : ∀ σ : ↥G, σ • (h : K) ∈ B := fun σ => hBG' σ _ h.2
  have hσhu : ∀ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ) ∉ IsLocalRing.maximalIdeal ↥Õ :=
    fun σ hσ => hhQ' σ ((memQ σ h).mpr hσ)
  set hp : K := ∏ σ : ↥G, σ • (h : K) with hhp
  have hp_B : hp ∈ B := Subring.prod_mem B (fun σ _ => hσhB σ)
  have hp_Õ : hp ∈ Õ := hBÕ hp_B
  have hpÕ_eq : ∀ hh : hp ∈ Õ, (⟨hp, hh⟩ : ↥Õ) = ∏ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ) := by
    intro hh
    apply Subtype.ext
    change hp = Õ.subtype (∏ σ : ↥G, (⟨σ • (h : K), hBÕ (hσhB σ)⟩ : ↥Õ))
    rw [map_prod, hhp]
    rfl
  have hp_unit : ∀ hh : hp ∈ Õ, IsUnit (⟨hp, hh⟩ : ↥Õ) := by
    intro hh
    rw [hpÕ_eq hh]
    apply Finset.prod_induction (p := fun x : ↥Õ => IsUnit x)
    · intro a b ha hb; exact ha.mul hb
    · exact isUnit_one
    · intro σ _
      have := hσhu σ
      rwa [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] at this
  have hpG : ∀ τ : ↥G, τ • hp = hp := by
    intro τ
    rw [hhp, Finset.smul_prod']
    simp_rw [smul_smul]
    exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ (fun σ => rfl)
  have hg'B : f * hp ∈ B := by
    have : hp = (h : K) * ∏ σ ∈ (Finset.univ : Finset ↥G).erase 1, σ • (h : K) := by
      rw [hhp, ← Finset.mul_prod_erase (Finset.univ : Finset ↥G) (fun σ => σ • (h : K)) (Finset.mem_univ 1), one_smul]
    rw [this, ← mul_assoc]
    exact B.mul_mem hfhB (Subring.prod_mem B (fun σ _ => hσhB σ))
  refine ⟨f * hp, hp, hg'B, hp_B, fun σ => ?_, hpG, hp_unit, rfl⟩
  rw [smul_mul', hfG, hpG]

end PartB

section RingC

variable (B BG Õ : Subring K) [IsLocalRing ↥Õ]

def Cring (hBGB : BG ≤ B) (hBÕ : B ≤ Õ) : Subring K where
  carrier := {f | ∃ b h : K, b ∈ B ∧ h ∈ BG ∧ ∃ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ) ∧ f * h = b}
  mul_mem' := by
    rintro f₁ f₂ ⟨b₁, h₁, hb₁, hh₁, hh₁Õ, hu₁, e₁⟩ ⟨b₂, h₂, hb₂, hh₂, hh₂Õ, hu₂, e₂⟩
    refine ⟨b₁ * b₂, h₁ * h₂, B.mul_mem hb₁ hb₂, BG.mul_mem hh₁ hh₂, Õ.mul_mem hh₁Õ hh₂Õ, ?_, ?_⟩
    · have : (⟨h₁ * h₂, Õ.mul_mem hh₁Õ hh₂Õ⟩ : ↥Õ) = ⟨h₁, hh₁Õ⟩ * ⟨h₂, hh₂Õ⟩ := rfl
      rw [this]; exact hu₁.mul hu₂
    · rw [← e₁, ← e₂]; ring
  one_mem' := ⟨1, 1, B.one_mem, BG.one_mem, Õ.one_mem, by
    have : (⟨(1 : K), Õ.one_mem⟩ : ↥Õ) = 1 := rfl
    rw [this]; exact isUnit_one, by ring⟩
  add_mem' := by
    rintro f₁ f₂ ⟨b₁, h₁, hb₁, hh₁, hh₁Õ, hu₁, e₁⟩ ⟨b₂, h₂, hb₂, hh₂, hh₂Õ, hu₂, e₂⟩
    refine ⟨b₁ * h₂ + b₂ * h₁, h₁ * h₂, B.add_mem (B.mul_mem hb₁ (hBGB hh₂)) (B.mul_mem hb₂ (hBGB hh₁)),
      BG.mul_mem hh₁ hh₂, Õ.mul_mem hh₁Õ hh₂Õ, ?_, ?_⟩
    · have : (⟨h₁ * h₂, Õ.mul_mem hh₁Õ hh₂Õ⟩ : ↥Õ) = ⟨h₁, hh₁Õ⟩ * ⟨h₂, hh₂Õ⟩ := rfl
      rw [this]; exact hu₁.mul hu₂
    · rw [← e₁, ← e₂]; ring
  zero_mem' := ⟨0, 1, B.zero_mem, BG.one_mem, Õ.one_mem, by
    have : (⟨(1 : K), Õ.one_mem⟩ : ↥Õ) = 1 := rfl
    rw [this]; exact isUnit_one, by ring⟩
  neg_mem' := by
    rintro f ⟨b, h, hb, hh, hhÕ, hu, e⟩
    exact ⟨-b, h, B.neg_mem hb, hh, hhÕ, hu, by rw [← e]; ring⟩

variable (hBGB : BG ≤ B) (hBÕ : B ≤ Õ)

theorem mem_Cring_iff (f : K) : f ∈ Cring B BG Õ hBGB hBÕ ↔
    ∃ b h : K, b ∈ B ∧ h ∈ BG ∧ ∃ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ) ∧ f * h = b := Iff.rfl

theorem le_Cring : B ≤ Cring B BG Õ hBGB hBÕ := fun b hb =>
  ⟨b, 1, hb, BG.one_mem, Õ.one_mem, by
    have : (⟨(1 : K), Õ.one_mem⟩ : ↥Õ) = 1 := rfl
    rw [this]; exact isUnit_one, by ring⟩

theorem Cring_le : Cring B BG Õ hBGB hBÕ ≤ Õ := by
  rintro f ⟨b, h, hb, hh, hhÕ, hu, e⟩
  obtain ⟨u, hu'⟩ := hu
  have hinv : ((u⁻¹ : (↥Õ)ˣ) : ↥Õ).val * h = 1 := by
    have := congrArg (fun z : ↥Õ => (z : K)) u.inv_mul
    rw [hu'] at this; exact this
  have : f = b * ((u⁻¹ : (↥Õ)ˣ) : ↥Õ).val := by
    calc f = f * (((u⁻¹ : (↥Õ)ˣ) : ↥Õ).val * h) := by rw [hinv, mul_one]
      _ = (f * h) * ((u⁻¹ : (↥Õ)ˣ) : ↥Õ).val := by ring
      _ = b * ((u⁻¹ : (↥Õ)ˣ) : ↥Õ).val := by rw [e]
  rw [this]
  exact Õ.mul_mem (hBÕ hb) ((u⁻¹ : (↥Õ)ˣ) : ↥Õ).2

theorem mem_Cring_of_frac {f b h : K} (hb : b ∈ B) (hh : h ∈ BG) (hhÕ : h ∈ Õ)
    (hu : IsUnit (⟨h, hhÕ⟩ : ↥Õ)) (e : f * h = b) : f ∈ Cring B BG Õ hBGB hBÕ :=
  ⟨b, h, hb, hh, hhÕ, hu, e⟩

end RingC

section RingC2

variable (G : Subgroup (K ≃ₐ[k] K)) (B BG Õ : Subring K) [IsLocalRing ↥Õ] (hBGB : BG ≤ B) (hBÕ : B ≤ Õ)
  (hBG' : ∀ (σ : ↥G) (f : K), f ∈ B → σ • f ∈ B) (hBGfix : ∀ (σ : ↥G) (h : K), h ∈ BG → σ • h = h)

include hBG' hBGfix in
theorem smul_mem_Cring (σ : ↥G) (f : K) (hf : f ∈ Cring B BG Õ hBGB hBÕ) : σ • f ∈ Cring B BG Õ hBGB hBÕ := by
  obtain ⟨b, h, hb, hh, hhÕ, hu, e⟩ := hf
  refine ⟨σ • b, h, hBG' σ b hb, hh, hhÕ, hu, ?_⟩
  conv_lhs => rw [← hBGfix σ h hh]
  rw [← smul_mul', e]

@[reducible] def Cact : MulSemiringAction ↥G ↥(Cring B BG Õ hBGB hBÕ) where
  smul σ c := ⟨σ • (c : K), smul_mem_Cring G B BG Õ hBGB hBÕ hBG' hBGfix σ _ c.2⟩
  one_smul c := Subtype.ext (one_smul (↥G) (c : K))
  mul_smul σ τ c := Subtype.ext (mul_smul σ τ (c : K))
  smul_zero σ := Subtype.ext (by change σ • ((0 : ↥(Cring B BG Õ hBGB hBÕ)) : K) = 0; rw [ZeroMemClass.coe_zero, smul_zero])
  smul_add σ x y := Subtype.ext (by
    change σ • ((x : K) + y) = σ • (x : K) + σ • (y : K); rw [smul_add])
  smul_one σ := Subtype.ext (by change σ • ((1 : ↥(Cring B BG Õ hBGB hBÕ)) : K) = 1; rw [OneMemClass.coe_one, smul_one])
  smul_mul σ x y := Subtype.ext (by
    change σ • ((x : K) * y) = σ • (x : K) * σ • (y : K); rw [smul_mul'])

theorem Cact_smul_val (σ : ↥G) (c : ↥(Cring B BG Õ hBGB hBÕ)) :
    (letI := Cact G B BG Õ hBGB hBÕ hBG' hBGfix; ((σ • c : ↥(Cring B BG Õ hBGB hBÕ)) : K)) = σ • (c : K) := rfl

end RingC2

section Levelwise

theorem map_maximalIdeal_eq_of_ringEquiv {A B : Type*} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (e : A ≃+* B) : (maximalIdeal A).map e.toRingHom = maximalIdeal B := by
  refine le_antisymm ?_ ?_
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hx
    intro hu; apply hx
    have := hu.map e.symm.toRingHom
    simpa using this
  · intro y hy
    have hy' : e.symm y ∈ maximalIdeal A := by
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hy ⊢
      intro hu; apply hy
      have := hu.map e.toRingHom
      simpa using this
    have := Ideal.mem_map_of_mem e.toRingHom hy'
    simpa using this

theorem evalₐ_ringEquiv_eq_zero {S : Type*} [CommRing S] [IsLocalRing S] [IsNoetherianRing S]
    (e : AdicCompletion (maximalIdeal S) S ≃+* AdicCompletion (maximalIdeal S) S) (n : ℕ)
    (x : AdicCompletion (maximalIdeal S) S) (hx : AdicCompletion.evalₐ (maximalIdeal S) n x = 0) :
    AdicCompletion.evalₐ (maximalIdeal S) n (e x) = 0 := by
  have hker : ∀ y : AdicCompletion (maximalIdeal S) S,
      AdicCompletion.evalₐ (maximalIdeal S) n y = 0 ↔ y ∈ maximalIdeal (AdicCompletion (maximalIdeal S) S) ^ n := by
    intro y
    rw [AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ n, RingHom.mem_ker]
  rw [hker] at hx ⊢
  have h1 : e x ∈ (maximalIdeal (AdicCompletion (maximalIdeal S) S) ^ n).map e.toRingHom :=
    Ideal.mem_map_of_mem e.toRingHom hx
  rwa [Ideal.map_pow, map_maximalIdeal_eq_of_ringEquiv e] at h1

end Levelwise

end QuotLoc
p2m_reactivate "P2MW.S_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization.QuotLoc"

open QuotLoc in
theorem solution
    {k K : Type*} [Field k] [Field K] [Algebra k K]
    (G : Subgroup (K ≃ₐ[k] K)) (hG : Finite ↥G)

    (B : Subring K) (hBG : ∀ σ : K ≃ₐ[k] K, σ ∈ G → ∀ f : K, f ∈ B → σ f ∈ B)
    (BG : Subring K) (hBGdef : ∀ f : K, f ∈ BG ↔ f ∈ B ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f)
    (hBGnoeth : IsNoetherianRing ↥BG)
    (hfin : ∀ (hle : BG ≤ B), letI := (Subring.inclusion hle).toAlgebra; Module.Finite ↥BG ↥B)

    (Õ : Subring K) [IsLocalRing ↥Õ] (hBÕ : B ≤ Õ)
    (hloc : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ B ∧ h ∈ B ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g)

    (H : Subgroup (K ≃ₐ[k] K)) (hH : ∀ σ : K ≃ₐ[k] K, σ ∈ H ↔ σ ∈ G ∧ ∀ f : K, f ∈ Õ ↔ σ f ∈ Õ)
    (O₀ : Subring K) (hO₀ : ∀ f : K, f ∈ O₀ ↔ f ∈ Õ ∧ ∀ σ : K ≃ₐ[k] K, σ ∈ G → σ f = f) :
    ∃ (_ : IsNoetherianRing ↥Õ) (_ : IsLocalRing ↥O₀) (_ : IsNoetherianRing ↥O₀) (hle : O₀ ≤ Õ)
      (act : ↥H → (AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ))
      (κ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ),

      (∀ f : ↥O₀, IsUnit f ↔ IsUnit (Subring.inclusion hle f)) ∧

      (∀ (σ : ↥H) (f : ↥Õ), ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ,
        act σ (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩) ∧
      (∀ (σ : ↥H) (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
        AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (act σ x) = 0) ∧
      (∀ (σ : ↥H) (F : AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
        (∀ f : ↥Õ, ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ, F (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩) →
        (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
          AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (F x) = 0) → F = act σ) ∧

      Function.Injective κ ∧
      (∀ f : ↥O₀, κ (algebraMap ↥O₀ _ f) = algebraMap ↥Õ _ (Subring.inclusion hle f)) ∧
      (∀ x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ, x ∈ Set.range κ ↔ ∀ σ : ↥H, act σ x = x) := by
  classical

  haveI hGfin : Finite ↥G := hG
  have hle : O₀ ≤ Õ := O₀_le G Õ O₀ hO₀
  haveI hO₀loc : IsLocalRing ↥O₀ := isLocalRing_O₀ G Õ O₀ hO₀
  have hunits : ∀ f : ↥O₀, IsUnit f ↔ IsUnit (Subring.inclusion hle f) := isUnit_iff G Õ O₀ hO₀
  have hBGB : BG ≤ B := fun f hf => ((hBGdef f).mp hf).1
  haveI hBGnoeth' : IsNoetherianRing ↥BG := hBGnoeth
  haveI hBnoeth : IsNoetherianRing ↥B := by
    letI : Algebra ↥BG ↥B := (Subring.inclusion hBGB).toAlgebra
    haveI : Module.Finite ↥BG ↥B := hfin hBGB
    exact IsNoetherianRing.of_finite ↥BG ↥B
  have hÕnoeth : IsNoetherianRing ↥Õ := isNoetherianRing_of_isLocalization B Õ hBÕ hloc
  haveI := hÕnoeth

  have hBG' : ∀ (σ : ↥G) (f : K), f ∈ B → σ • f ∈ B := fun σ f hf => hBG σ σ.2 f hf
  have hBGfix : ∀ (σ : ↥G) (h : K), h ∈ BG → σ • h = h := fun σ h hh => ((hBGdef h).mp hh).2 σ σ.2
  have hO₀fix : ∀ (σ : ↥G) (h : K), h ∈ O₀ → σ • h = h := fun σ h hh => ((hO₀ h).mp hh).2 σ σ.2
  have hBGO₀ : BG ≤ O₀ := fun f hf => (hO₀ f).mpr ⟨hBÕ (hBGB hf), ((hBGdef f).mp hf).2⟩

  have hlocO₀ : ∀ f : K, f ∈ O₀ ↔ ∃ g h : K, g ∈ BG ∧ h ∈ BG ∧
      (∀ hh : h ∈ O₀, IsUnit (⟨h, hh⟩ : ↥O₀)) ∧ f * h = g := by
    intro f
    constructor
    · intro hf
      obtain ⟨g, h, hgB, hhB, hgG, hhG, hhu, e⟩ :=
        exists_invariant_fraction G B hBG Õ hBÕ hloc f (hle hf) (fun σ => hO₀fix σ f hf)
      refine ⟨g, h, (hBGdef g).mpr ⟨hgB, fun σ hσ => hgG ⟨σ, hσ⟩⟩, (hBGdef h).mpr ⟨hhB, fun σ hσ => hhG ⟨σ, hσ⟩⟩,
        fun hh => (hunits ⟨h, hh⟩).mpr (hhu (hle hh)), e⟩
    · rintro ⟨g, h, hg, hh, hhu, e⟩
      obtain ⟨u, hu⟩ := hhu (hBGO₀ hh)
      have hinv : (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h = 1 := by
        have := congrArg (fun z : ↥O₀ => (z : K)) u.inv_mul
        rw [hu] at this; exact this
      have : f = g * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by
        calc f = f * ((((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h) := by rw [hinv, mul_one]
          _ = (f * h) * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by ring
          _ = g * (((u⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) := by rw [e]
      rw [this]
      exact O₀.mul_mem (hBGO₀ hg) ((u⁻¹ : (↥O₀)ˣ) : ↥O₀).2
  haveI hO₀noeth : IsNoetherianRing ↥O₀ := isNoetherianRing_of_isLocalization BG O₀ hBGO₀ hlocO₀

  have hBC : B ≤ Cring B BG Õ hBGB hBÕ := le_Cring B BG Õ hBGB hBÕ
  have hCÕ : Cring B BG Õ hBGB hBÕ ≤ Õ := Cring_le B BG Õ hBGB hBÕ
  have hO₀C : O₀ ≤ Cring B BG Õ hBGB hBÕ := by
    intro f hf
    obtain ⟨g, h, hg, hh, hhu, e⟩ := (hlocO₀ f).mp hf
    exact mem_Cring_of_frac B BG Õ hBGB hBÕ (hBGB hg) hh (hle (hBGO₀ hh))
      ((hunits ⟨h, hBGO₀ hh⟩).mp (hhu (hBGO₀ hh))) e

  set C : Subring K := Cring B BG Õ hBGB hBÕ with hCdef
  letI algO₀C : Algebra ↥O₀ ↥C := (Subring.inclusion hO₀C).toAlgebra
  letI algCÕ : Algebra ↥C ↥Õ := (Subring.inclusion hCÕ).toAlgebra
  letI actC : MulSemiringAction ↥G ↥C := Cact G B BG Õ hBGB hBÕ hBG' hBGfix
  have hsmulC : ∀ (σ : ↥G) (c : ↥C), ((σ • c : ↥C) : K) = σ • (c : K) := fun _ _ => rfl
  have halgO₀C : ∀ a : ↥O₀, (algebraMap ↥O₀ ↥C a : K) = (a : K) := fun _ => rfl
  have halgCÕ : ∀ c : ↥C, (algebraMap ↥C ↥Õ c : K) = (c : K) := fun _ => rfl
  haveI : SMulCommClass ↥G ↥O₀ ↥C := ⟨fun σ a c => Subtype.ext (by
    change σ • ((a : K) * (c : K)) = (a : K) * (σ • (c : K))
    rw [smul_mul', hO₀fix σ _ a.2])⟩
  haveI : FaithfulSMul ↥O₀ ↥C := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    (fun a b h => Subtype.ext (by have := congrArg (fun z : ↥C => (z : K)) h; exact this))
  haveI : Algebra.IsInvariant ↥O₀ ↥C ↥G := ⟨fun c hc =>
    ⟨⟨(c : K), (hO₀ c).mpr ⟨hCÕ c.2, fun σ hσ => by
      have := congrArg (fun z : ↥C => (z : K)) (hc ⟨σ, hσ⟩); exact this⟩⟩, Subtype.ext rfl⟩⟩
  haveI : Module.Finite ↥O₀ ↥C := by
    letI algBGB : Algebra ↥BG ↥B := (Subring.inclusion hBGB).toAlgebra
    haveI : Module.Finite ↥BG ↥B := hfin hBGB
    obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ↥BG) (M := ↥B)
    let ι : ↥B → ↥C := fun b => ⟨(b : K), hBC b.2⟩
    refine ⟨⟨S.image ι, ?_⟩⟩
    rw [eq_top_iff]
    rintro c -
    obtain ⟨b, h, hb, hh, hhÕ, hu, e⟩ := c.2
    have hhO₀ : h ∈ O₀ := hBGO₀ hh
    have hhu : IsUnit (⟨h, hhO₀⟩ : ↥O₀) := (hunits ⟨h, hhO₀⟩).mpr hu
    obtain ⟨v, hv⟩ := hhu
    have key : ∀ x : ↥B, x ∈ Submodule.span ↥BG (S : Set ↥B) →
        ι x ∈ Submodule.span ↥O₀ ((S.image ι : Finset ↥C) : Set ↥C) := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hxS => exact Submodule.subset_span (by
          rw [Finset.coe_image]; exact Set.mem_image_of_mem ι hxS)
      | zero => have : ι 0 = 0 := Subtype.ext rfl; rw [this]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => have : ι (x + y) = ι x + ι y := Subtype.ext rfl; rw [this]; exact Submodule.add_mem _ hx hy
      | smul a x _ hx =>
          have : ι (a • x) = (⟨(a : K), hBGO₀ a.2⟩ : ↥O₀) • ι x := Subtype.ext rfl
          rw [this]; exact Submodule.smul_mem _ _ hx
    have hbspan : ι ⟨b, hb⟩ ∈ Submodule.span ↥O₀ ((S.image ι : Finset ↥C) : Set ↥C) :=
      key _ (by rw [hS]; exact Submodule.mem_top)
    have hinv : (((v⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h = 1 := by
      have := congrArg (fun z : ↥O₀ => (z : K)) v.inv_mul
      rw [hv] at this; exact this
    have hc : c = ((v⁻¹ : (↥O₀)ˣ) : ↥O₀) • ι ⟨b, hb⟩ := by
      apply Subtype.ext
      change (c : K) = (((v⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * b
      calc (c : K) = (c : K) * ((((v⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * h) := by rw [hinv, mul_one]
        _ = (((v⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * ((c : K) * h) := by ring
        _ = (((v⁻¹ : (↥O₀)ˣ) : ↥O₀) : K) * b := by rw [e]
    rw [hc]
    exact Submodule.smul_mem _ _ hbspan

  set 𝔫 : Ideal ↥C := (maximalIdeal ↥Õ).comap (algebraMap ↥C ↥Õ) with h𝔫def
  have mem𝔫 : ∀ c : ↥C, c ∈ 𝔫 ↔ ¬ IsUnit (⟨(c : K), hCÕ c.2⟩ : ↥Õ) := by
    intro c; rw [h𝔫def, Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]; rfl
  haveI h𝔫prime : 𝔫.IsPrime := Ideal.comap_isPrime _ _
  have h𝔫under : 𝔫.comap (algebraMap ↥O₀ ↥C) = maximalIdeal ↥O₀ := by
    ext a
    rw [Ideal.mem_comap, mem𝔫, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hunits a]
    rfl
  haveI h𝔫over : 𝔫.LiesOver (maximalIdeal ↥O₀) := ⟨by rw [Ideal.under_def, h𝔫under]⟩
  haveI : Algebra.IsIntegral ↥O₀ ↥C := Algebra.IsIntegral.of_finite ↥O₀ ↥C
  haveI h𝔫max : 𝔫.IsMaximal :=
    Ideal.isMaximal_of_isIntegral_of_isMaximal_comap 𝔫 (by rw [h𝔫under]; exact IsLocalRing.maximalIdeal.isMaximal ↥O₀)

  have hlocC : ∀ f : K, f ∈ Õ ↔ ∃ g h : K, g ∈ C ∧ h ∈ C ∧ (∀ hh : h ∈ Õ, IsUnit (⟨h, hh⟩ : ↥Õ)) ∧ f * h = g := by
    intro f; constructor
    · intro hf
      obtain ⟨g, h, hg, hh, hu, e⟩ := (hloc f).mp hf
      exact ⟨g, h, hBC hg, hBC hh, hu, e⟩
    · rintro ⟨g, h, hg, hh, hhu, e⟩
      obtain ⟨u, hu⟩ := hhu (hCÕ hh)
      have hinv : (((u⁻¹ : (↥Õ)ˣ) : ↥Õ) : K) * h = 1 := by
        have := congrArg (fun z : ↥Õ => (z : K)) u.inv_mul
        rw [hu] at this; exact this
      have : f = g * (((u⁻¹ : (↥Õ)ˣ) : ↥Õ) : K) := by
        calc f = f * ((((u⁻¹ : (↥Õ)ˣ) : ↥Õ) : K) * h) := by rw [hinv, mul_one]
          _ = (f * h) * (((u⁻¹ : (↥Õ)ˣ) : ↥Õ) : K) := by ring
          _ = g * (((u⁻¹ : (↥Õ)ˣ) : ↥Õ) : K) := by rw [e]
      rw [this]
      exact Õ.mul_mem (hCÕ hg) ((u⁻¹ : (↥Õ)ˣ) : ↥Õ).2
  haveI hlocat : IsLocalization.AtPrime ↥Õ 𝔫 := isLocalization_ctr C Õ hCÕ hlocC

  obtain ⟨hinv, hinj, -, -⟩ :=
    Algebra.IsInvariant.isInvariant_adicCompletion_stabilizer_and_injective_and_finite (O := ↥O₀) (G := ↥G) 𝔫
  obtain ⟨T, hT⟩ := AdicCompletion.exists_ringEquiv_of_isLocalization_atPrime_of_isMaximal (S := ↥Õ) 𝔫

  have hunitK : ∀ (S : Subring K) (f : K) (hf : f ∈ S), IsUnit (⟨f, hf⟩ : ↥S) ↔ ∃ g : K, g ∈ S ∧ f * g = 1 := by
    intro S f hf
    constructor
    · rintro ⟨u, hu⟩
      refine ⟨((u⁻¹ : (↥S)ˣ) : ↥S), ((u⁻¹ : (↥S)ˣ) : ↥S).2, ?_⟩
      have := congrArg (fun z : ↥S => (z : K)) u.mul_inv
      rw [hu] at this; exact this
    · rintro ⟨g, hg, e⟩
      exact isUnit_iff_exists_inv.mpr ⟨⟨g, hg⟩, Subtype.ext e⟩
  have hunit_pres : ∀ (γ : ↥G), (∀ f : K, f ∈ Õ ↔ γ • f ∈ Õ) →
      ∀ (f : K) (hf : f ∈ Õ) (hγf : γ • f ∈ Õ), IsUnit (⟨f, hf⟩ : ↥Õ) → IsUnit (⟨γ • f, hγf⟩ : ↥Õ) := by
    intro γ hγ f hf hγf hu
    rw [hunitK] at hu ⊢
    obtain ⟨g, hg, e⟩ := hu
    exact ⟨γ • g, (hγ g).mp hg, by rw [← smul_mul', e, smul_one]⟩
  have hpres_inv : ∀ (γ : ↥G), (∀ f : K, f ∈ Õ ↔ γ • f ∈ Õ) → ∀ f : K, f ∈ Õ ↔ γ⁻¹ • f ∈ Õ := by
    intro γ hγ f
    conv_lhs => rw [← smul_inv_smul γ f]
    exact (hγ (γ⁻¹ • f)).symm
  have stab_of_pres : ∀ γ : ↥G, (∀ f : K, f ∈ Õ ↔ γ • f ∈ Õ) → γ ∈ MulAction.stabilizer ↥G 𝔫 := by
    intro γ hγ
    rw [MulAction.mem_stabilizer_iff]
    ext c
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, mem𝔫, mem𝔫, not_iff_not]
    constructor
    · intro hu
      have h1 := hunit_pres γ hγ _ (hCÕ (γ⁻¹ • c).2) (by rw [hsmulC, smul_inv_smul]; exact hCÕ c.2) hu
      have : (⟨γ • ((γ⁻¹ • c : ↥C) : K), by rw [hsmulC, smul_inv_smul]; exact hCÕ c.2⟩ : ↥Õ) = ⟨(c : K), hCÕ c.2⟩ := by
        apply Subtype.ext; change γ • ((γ⁻¹ • c : ↥C) : K) = (c : K); rw [hsmulC, smul_inv_smul]
      rwa [this] at h1
    · intro hu
      exact hunit_pres γ⁻¹ (hpres_inv γ hγ) _ (hCÕ c.2) (hCÕ (γ⁻¹ • c).2) hu
  have pres_of_stab_aux : ∀ γ : ↥G, γ ∈ MulAction.stabilizer ↥G 𝔫 → ∀ f : K, f ∈ Õ → γ • f ∈ Õ := by
    intro γ hγ f hf
    rw [MulAction.mem_stabilizer_iff] at hγ
    obtain ⟨g, h, hg, hh, hhu, e⟩ := (hlocC f).mp hf
    have hhn : (⟨h, hh⟩ : ↥C) ∉ 𝔫 := fun hn => (mem𝔫 _).mp hn (hhu (hCÕ hh))
    have hγhn : (γ • (⟨h, hh⟩ : ↥C)) ∉ 𝔫 := by
      intro hn; apply hhn
      rw [← hγ] at hn
      exact Ideal.smul_mem_pointwise_smul_iff.mp hn
    rw [mem𝔫, not_not] at hγhn
    refine (hlocC (γ • f)).mpr ⟨γ • g, γ • h, (γ • (⟨g, hg⟩ : ↥C)).2, (γ • (⟨h, hh⟩ : ↥C)).2, fun hh' => hγhn, ?_⟩
    rw [← smul_mul', e]
  have pres_of_stab : ∀ γ : ↥G, γ ∈ MulAction.stabilizer ↥G 𝔫 → ∀ f : K, f ∈ Õ ↔ γ • f ∈ Õ := by
    intro γ hγ f
    constructor
    · exact pres_of_stab_aux γ hγ f
    · intro hf
      have := pres_of_stab_aux γ⁻¹ (Subgroup.inv_mem _ hγ) _ hf
      rwa [inv_smul_smul] at this

  have hHmem : ∀ σ : ↥H, (σ : K ≃ₐ[k] K) ∈ G ∧ ∀ f : K, f ∈ Õ ↔ (σ : K ≃ₐ[k] K) f ∈ Õ := fun σ => (hH σ).mp σ.2
  let toG : ↥H → ↥G := fun σ => ⟨(σ : K ≃ₐ[k] K), (hHmem σ).1⟩
  have toG_smul : ∀ (σ : ↥H) (f : K), toG σ • f = (σ : K ≃ₐ[k] K) f := fun _ _ => rfl
  let toStab : ↥H → ↥(MulAction.stabilizer ↥G 𝔫) := fun σ =>
    ⟨toG σ, stab_of_pres (toG σ) (fun f => by rw [toG_smul]; exact (hHmem σ).2 f)⟩
  have toStab_surj : ∀ d : ↥(MulAction.stabilizer ↥G 𝔫), ∃ σ : ↥H, toStab σ = d := by
    intro d
    refine ⟨⟨((d : ↥G) : K ≃ₐ[k] K), (hH _).mpr ⟨(d : ↥G).2, pres_of_stab _ d.2⟩⟩, ?_⟩
    apply Subtype.ext; apply Subtype.ext; rfl

  have hofC : ∀ c : ↥C, algebraMap ↥C (AdicCompletion 𝔫 ↥C) c = AdicCompletion.of 𝔫 ↥C c := fun c => by
    rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hofÕ : ∀ f : ↥Õ, algebraMap ↥Õ (AdicCompletion (maximalIdeal ↥Õ) ↥Õ) f = AdicCompletion.of (maximalIdeal ↥Õ) ↥Õ f :=
    fun f => by rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hofO₀ : ∀ a : ↥O₀, algebraMap ↥O₀ (AdicCompletion (maximalIdeal ↥O₀) ↥O₀) a = AdicCompletion.of (maximalIdeal ↥O₀) ↥O₀ a :=
    fun a => by rw [AdicCompletion.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
  have hTsymm : ∀ c : ↥C, T.symm (algebraMap ↥Õ _ (algebraMap ↥C ↥Õ c)) = algebraMap ↥C _ c := by
    intro c; rw [← hT c, RingEquiv.symm_apply_apply]
  let actEquiv : ↥H → (AdicCompletion (maximalIdeal ↥Õ) ↥Õ ≃+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ) := fun σ =>
    T.symm.trans ((MulSemiringAction.toRingEquiv _ (AdicCompletion 𝔫 ↥C) (toStab σ)).trans T)
  have actEquiv_apply : ∀ (σ : ↥H) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
      actEquiv σ x = T (toStab σ • T.symm x) := fun _ _ => rfl
  let act : ↥H → (AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ) :=
    fun σ => (actEquiv σ).toRingHom
  have act_apply : ∀ (σ : ↥H) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ), act σ x = T (toStab σ • T.symm x) :=
    fun _ _ => rfl
  let κ : AdicCompletion (maximalIdeal ↥O₀) ↥O₀ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ :=
    T.toRingHom.comp (algebraMap (AdicCompletion (maximalIdeal ↥O₀) ↥O₀) (AdicCompletion 𝔫 ↥C))
  have κ_apply : ∀ a, κ a = T (algebraMap (AdicCompletion (maximalIdeal ↥O₀) ↥O₀) (AdicCompletion 𝔫 ↥C) a) :=
    fun _ => rfl

  have act_ofC : ∀ (σ : ↥H) (c : ↥C),
      act σ (algebraMap ↥Õ _ (algebraMap ↥C ↥Õ c)) = algebraMap ↥Õ _ (algebraMap ↥C ↥Õ ((toStab σ : ↥G) • c)) := by
    intro σ c
    rw [act_apply, hTsymm, hofC, AdicCompletion.stabilizer_smul_of, ← hofC, hT]

  have act_of : ∀ (σ : ↥H) (f : ↥Õ), ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ,
      act σ (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩ := by
    intro σ f
    have hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ := ((hHmem σ).2 f).mp f.2
    refine ⟨hσf, ?_⟩
    obtain ⟨g, h, hg, hh, hhu, e⟩ := (hlocC f).mp f.2
    have hσh : (σ : K ≃ₐ[k] K) h ∈ Õ := ((hHmem σ).2 h).mp (hCÕ hh)
    have hσhu : IsUnit (⟨(σ : K ≃ₐ[k] K) h, hσh⟩ : ↥Õ) := by
      have := hunit_pres (toG σ) (fun f => by rw [toG_smul]; exact (hHmem σ).2 f) h (hCÕ hh)
        (by rw [toG_smul]; exact hσh) (hhu (hCÕ hh))
      exact this

    have e1 : f * (⟨h, hCÕ hh⟩ : ↥Õ) = ⟨g, hCÕ hg⟩ := Subtype.ext e
    have e2 : (⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩ : ↥Õ) * ⟨(σ : K ≃ₐ[k] K) h, hσh⟩ = ⟨(σ : K ≃ₐ[k] K) g, ((hHmem σ).2 g).mp (hCÕ hg)⟩ := by
      apply Subtype.ext
      change (σ : K ≃ₐ[k] K) (f : K) * (σ : K ≃ₐ[k] K) h = (σ : K ≃ₐ[k] K) g
      rw [← map_mul, e]
    have hh' : algebraMap ↥C ↥Õ ⟨h, hh⟩ = ⟨h, hCÕ hh⟩ := rfl
    have hg' : algebraMap ↥C ↥Õ ⟨g, hg⟩ = ⟨g, hCÕ hg⟩ := rfl
    have hσh' : algebraMap ↥C ↥Õ ((toStab σ : ↥G) • (⟨h, hh⟩ : ↥C)) = ⟨(σ : K ≃ₐ[k] K) h, hσh⟩ := Subtype.ext rfl
    have hσg' : algebraMap ↥C ↥Õ ((toStab σ : ↥G) • (⟨g, hg⟩ : ↥C)) = ⟨(σ : K ≃ₐ[k] K) g, ((hHmem σ).2 g).mp (hCÕ hg)⟩ :=
      Subtype.ext rfl
    have key : act σ (algebraMap ↥Õ _ f) * algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) h, hσh⟩ =
        algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩ * algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) h, hσh⟩ := by
      rw [← map_mul (algebraMap ↥Õ (AdicCompletion (maximalIdeal ↥Õ) ↥Õ)), e2, ← hσg', ← act_ofC, hg', ← e1, map_mul,
        map_mul, ← hh', act_ofC, hσh']
    exact (IsUnit.mul_left_inj ((hσhu.map (algebraMap ↥Õ (AdicCompletion (maximalIdeal ↥Õ) ↥Õ))))).mp key

  have act_lev : ∀ (σ : ↥H) (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
      AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (act σ x) = 0 :=
    fun σ n x hx => evalₐ_ringEquiv_eq_zero (actEquiv σ) n x hx

  have hker : ∀ (n : ℕ) (y : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
      y ∈ ((maximalIdeal ↥Õ) ^ n).map (algebraMap ↥Õ (AdicCompletion (maximalIdeal ↥Õ) ↥Õ)) →
        AdicCompletion.evalₐ (maximalIdeal ↥Õ) n y = 0 := by
    intro n y hy
    rw [Ideal.map_pow, ← AdicCompletion.maximalIdeal_eq_map, AdicCompletion.maximalIdeal_pow_eq_ker_evalₐ n] at hy
    exact hy

  have act_uniq : ∀ (σ : ↥H) (F : AdicCompletion (maximalIdeal ↥Õ) ↥Õ →+* AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
      (∀ f : ↥Õ, ∃ hσf : (σ : K ≃ₐ[k] K) (f : K) ∈ Õ, F (algebraMap ↥Õ _ f) = algebraMap ↥Õ _ ⟨(σ : K ≃ₐ[k] K) (f : K), hσf⟩) →
      (∀ (n : ℕ) (x : AdicCompletion (maximalIdeal ↥Õ) ↥Õ),
        AdicCompletion.evalₐ (maximalIdeal ↥Õ) n x = 0 → AdicCompletion.evalₐ (maximalIdeal ↥Õ) n (F x) = 0) → F = act σ := by
    intro σ F hF hFlev
    apply RingHom.ext
    intro x
    apply AdicCompletion.ext_evalₐ
    intro n
    obtain ⟨a, y, hy, rfl⟩ := AdicCompletion.exists_eq_algebraMap_add (maximalIdeal ↥Õ) (IsNoetherian.noetherian _) n x
    obtain ⟨h1, e1⟩ := hF a
    obtain ⟨h2, e2⟩ := act_of σ a
    rw [map_add, map_add, map_add, map_add, hFlev n y (hker n y hy), act_lev σ n y (hker n y hy), e1, e2]

  refine ⟨hÕnoeth, hO₀loc, hO₀noeth, hle, act, κ, hunits, act_of, act_lev, act_uniq, ?_, ?_, ?_⟩
  ·
    exact T.injective.comp hinj
  ·
    intro f
    rw [κ_apply, hofO₀, AdicCompletion.algebraMap_of, ← hofC, hT]
    rfl
  ·
    intro x
    constructor
    · rintro ⟨a, rfl⟩ σ
      rw [act_apply, κ_apply, RingEquiv.symm_apply_apply, AdicCompletion.stabilizer_smul_algebraMap]
    · intro hx
      have hx' : ∀ d : ↥(MulAction.stabilizer ↥G 𝔫), d • T.symm x = T.symm x := by
        intro d
        obtain ⟨σ, rfl⟩ := toStab_surj d
        have := hx σ
        rw [act_apply] at this
        calc toStab σ • T.symm x = T.symm (T (toStab σ • T.symm x)) := by rw [RingEquiv.symm_apply_apply]
          _ = T.symm x := by rw [this]
      obtain ⟨a, ha⟩ := hinv.isInvariant (T.symm x) hx'
      refine ⟨a, ?_⟩
      rw [κ_apply, ha, RingEquiv.apply_symm_apply]

end S_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization
end P2MW
export P2MW.S_IsLocalRing_exists_ringHom_adicCompletion_inf_fixedPoints_range_eq_of_isLocalization (solution)
