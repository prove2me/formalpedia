-- Prove2me | solution 1 for HeckeEis.isEigensystemH1_of_isEigensystemH1_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/fc84ca29-8464-5eeb-8fe0-76f09bd58e4b

import Mathlib
import Definitions.Def_Gamma0HeckeOperatorHom
import Definitions.Def_Gamma0CoeffCohomology
import Definitions.Def_Gamma0CoeffCohomologyEigen
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCocycles
import Theorems.Thm_HeckeEis_coeffHeckeFun_mem_coeffCoboundaries
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange

set_option autoImplicit false

open CongruenceSubgroup HeckeEis

namespace BCChi

section Induced

variable {K : Type} [CommRing K] {V : Type} [AddCommGroup V] [Module K V]
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

end Induced

section Carry

variable {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (N : ℕ)
variable {V₀ V : Type} [AddCommGroup V₀] [Module K₀ V₀] [AddCommGroup V] [Module K V]
variable (ρ₀ : Representation K₀ (Gamma0 N) V₀) (ρ : Representation K (Gamma0 N) V)
variable (j : V₀ →ₛₗ[i] V) (hj : ∀ (g : Gamma0 N) (v : V₀), j (ρ₀ g v) = ρ g (j v))

include hj in
theorem carry_mem_coeffCocycles (z : ↥(coeffCocycles ρ₀)) : (fun g => j ((z : Gamma0 N → V₀) g)) ∈ coeffCocycles ρ := by
  rw [mem_coeffCocycles_iff]
  intro g h
  rw [(mem_coeffCocycles_iff ρ₀ _).mp z.2 g h, map_add, hj]

def carry (z : ↥(coeffCocycles ρ₀)) : ↥(coeffCocycles ρ) := ⟨_, carry_mem_coeffCocycles i N ρ₀ ρ j hj z⟩

@[scoped simp] theorem coe_carry (z : ↥(coeffCocycles ρ₀)) (g : Gamma0 N) :
    (carry i N ρ₀ ρ j hj z : Gamma0 N → V) g = j ((z : Gamma0 N → V₀) g) := rfl

include hj in
theorem carry_coeffHeckeFun (ℓ : ℕ) [NeZero ℓ] (a₀ : V₀ →ₗ[K₀] V₀) (a : V →ₗ[K] V)
    (hja : ∀ v : V₀, j (a₀ v) = a (j v)) (z : Gamma0 N → V₀) (g : Gamma0 N) :
    j (coeffHeckeFun N ℓ ρ₀ a₀ z g) = coeffHeckeFun N ℓ ρ a (fun g => j (z g)) g := by
  letI := (heckeUpper N ℓ).fintypeQuotientOfFiniteIndex
  rw [coeffHeckeFun_apply, coeffHeckeFun_apply, map_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [hj, hja]

end Carry

section Retract

variable {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (N : ℕ)
variable {V₀ V : Type} [AddCommGroup V₀] [Module K₀ V₀] [AddCommGroup V] [Module K V]
variable (ρ₀ : Representation K₀ (Gamma0 N) V₀) (ρ : Representation K (Gamma0 N) V)
variable (j : V₀ →ₛₗ[i] V) (hj : ∀ (g : Gamma0 N) (v : V₀), j (ρ₀ g v) = ρ g (j v))
variable {ι : Type} (b₀ : Module.Basis ι K₀ V₀) (b : Module.Basis ι K V) (hb : ∀ s : ι, b s = j (b₀ s))

theorem exists_retraction : ∃ r : K →+ K₀, (∀ c : K₀, r (i c) = c) ∧ ∀ (m : K₀) (c : K), r (i m * c) = m * r c := by
  letI : Module K₀ K := Module.compHom K i
  let iₗ : K₀ →ₗ[K₀] K :=
    { toFun := i, map_add' := i.map_add, map_smul' := fun m c => by
        show i (m * c) = i m * i c
        exact map_mul i m c }
  have hinj : LinearMap.ker iₗ = ⊥ := LinearMap.ker_eq_bot.mpr i.injective
  obtain ⟨r, hr⟩ := iₗ.exists_leftInverse_of_injective hinj
  refine ⟨r.toAddMonoidHom, fun c => ?_, fun m c => ?_⟩
  · exact congrArg (fun f : K₀ →ₗ[K₀] K₀ => f c) hr
  · exact r.map_smul m c

include hb in

theorem j_linearCombination (f : ι →₀ K₀) :
    j (Finsupp.linearCombination K₀ b₀ f) = Finsupp.linearCombination K b (Finsupp.mapRange i (map_zero i) f) := by
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply,
    Finsupp.sum_mapRange_index (fun s => by simp), map_finsuppSum]
  refine Finsupp.sum_congr fun s c => ?_
  rw [LinearMap.map_smulₛₗ, hb]

include hb in
theorem repr_j (v₀ : V₀) : b.repr (j v₀) = Finsupp.mapRange i (map_zero i) (b₀.repr v₀) := by
  conv_lhs => rw [← b₀.linearCombination_repr v₀, j_linearCombination i j b₀ b hb]
  rw [b.repr_linearCombination]

include hb hj in

theorem mem_coeffCoboundaries_of_carry (z₀ : Gamma0 N → V₀)
    (h : (fun g => j (z₀ g)) ∈ coeffCoboundaries ρ) : z₀ ∈ coeffCoboundaries ρ₀ := by
  classical
  obtain ⟨r, hr, hr'⟩ := exists_retraction i
  rw [mem_coeffCoboundaries_iff] at h ⊢
  obtain ⟨v, hv⟩ := h

  let Rf : (ι →₀ K) →+ (ι →₀ K₀) := Finsupp.mapRange.addMonoidHom r
  let R : V →+ V₀ :=
    (Finsupp.linearCombination K₀ b₀).toAddMonoidHom.comp (Rf.comp b.repr.toLinearMap.toAddMonoidHom)
  have hRapply : ∀ w : V, R w = Finsupp.linearCombination K₀ b₀ (Finsupp.mapRange r (map_zero r) (b.repr w)) :=
    fun w => rfl

  have hRj : ∀ v₀ : V₀, R (j v₀) = v₀ := by
    intro v₀
    rw [hRapply, repr_j i j b₀ b hb]
    have : Finsupp.mapRange r (map_zero r) (Finsupp.mapRange i (map_zero i) (b₀.repr v₀)) = b₀.repr v₀ := by
      ext t; simp [hr]
    rw [this, b₀.linearCombination_repr]

  have hRρ : ∀ (g : Gamma0 N) (w : V), R (ρ g w) = ρ₀ g (R w) := by
    intro g w

    suffices hmaps : R.comp ((ρ g).toAddMonoidHom.comp (Finsupp.linearCombination K b).toAddMonoidHom) =
        (ρ₀ g).toAddMonoidHom.comp (R.comp (Finsupp.linearCombination K b).toAddMonoidHom) by
      have := congrArg (fun F : (ι →₀ K) →+ V₀ => F (b.repr w)) hmaps
      simpa [b.linearCombination_repr] using this
    refine Finsupp.addHom_ext fun s c => ?_
    have e1 : Finsupp.linearCombination K b (Finsupp.single s c) = c • b s := by
      rw [Finsupp.linearCombination_single]
    have e2 : b.repr (ρ g (c • b s)) = c • Finsupp.mapRange i (map_zero i) (b₀.repr (ρ₀ g (b₀ s))) := by
      rw [map_smul, map_smul, hb, ← hj, repr_j i j b₀ b hb]
    have e3 : Finsupp.mapRange r (map_zero r) (c • Finsupp.mapRange i (map_zero i) (b₀.repr (ρ₀ g (b₀ s)))) =
        r c • b₀.repr (ρ₀ g (b₀ s)) := by
      ext t
      simp only [Finsupp.mapRange_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul]
      rw [mul_comm, hr', mul_comm]
    have e4 : b.repr (c • b s) = c • Finsupp.single s 1 := by rw [map_smul, b.repr_self]
    have e5 : Finsupp.mapRange r (map_zero r) (c • Finsupp.single s (1 : K)) = Finsupp.single s (r c) := by
      ext t
      simp only [Finsupp.mapRange_apply, Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply]
      split_ifs <;> simp
    show R (ρ g (Finsupp.linearCombination K b (Finsupp.single s c))) = ρ₀ g (R (Finsupp.linearCombination K b (Finsupp.single s c)))
    rw [e1, hRapply, hRapply, e2, e3, e4, e5, map_smul, b₀.linearCombination_repr, Finsupp.linearCombination_single, map_smul]

  refine ⟨R v, funext fun g => ?_⟩
  have := congrArg R (congrFun hv g)
  rw [hRj, map_sub, hRρ] at this
  exact this

end Retract

section Main

theorem main (N : ℕ) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (S₀ : Set ℕ)
    {V₀ V : Type} [AddCommGroup V₀] [Module K₀ V₀] [AddCommGroup V] [Module K V]
    (ρ₀ : Representation K₀ (CongruenceSubgroup.Gamma0 N) V₀) (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (a₀ : ℕ → (V₀ →ₗ[K₀] V₀)) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (j : V₀ →ₛₗ[i] V) (hj : ∀ (g : CongruenceSubgroup.Gamma0 N) (v : V₀), j (ρ₀ g v) = ρ g (j v))
    (hja : ∀ (ℓ : ℕ) (v : V₀), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → j (a₀ ℓ v) = a ℓ (j v))
    (hbc : ∃ (ι : Type) (b₀ : Module.Basis ι K₀ V₀) (b : Module.Basis ι K V), ∀ s : ι, b s = j (b₀ s))
    (lam : ℕ → K₀) (h : HeckeEis.IsEigensystemH1 N ρ₀ a₀ S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ (fun ℓ => i (lam ℓ)) := by
  obtain ⟨ι, b₀, b, hb⟩ := hbc
  obtain ⟨x₀, hx₀, hT₀⟩ := h
  obtain ⟨z₀, rfl⟩ := coeffH1Mk_surjective ρ₀ x₀
  refine ⟨coeffH1Mk ρ (carry i N ρ₀ ρ j hj z₀), ?_, ?_⟩
  ·
    intro h0
    apply hx₀
    rw [coeffH1Mk_eq_zero_iff] at h0 ⊢
    exact mem_coeffCoboundaries_of_carry i N ρ₀ ρ j hj b₀ b hb _ h0
  · intro ℓ hℓ hℓN hℓS
    haveI : NeZero ℓ := ⟨hℓ.ne_zero⟩
    obtain ⟨T₀, hT₀def, hT₀x⟩ := hT₀ ℓ hℓ hℓN hℓS
    have hac : IsCompat N ℓ ρ (a ℓ) := fun u => ha ℓ hℓ hℓN hℓS u
    refine ⟨heckeH1 hac, isCoeffHeckeOnH1_heckeH1 hac, ?_⟩

    obtain ⟨w₀, hw₀, hT₀z⟩ := hT₀def z₀
    have hcob : ((w₀ : Gamma0 N → V₀) - lam ℓ • (z₀ : Gamma0 N → V₀)) ∈ coeffCoboundaries ρ₀ := by
      have : coeffH1Mk ρ₀ (w₀ - lam ℓ • z₀) = 0 := by rw [map_sub, map_smul, ← hT₀z, hT₀x, sub_self]
      rw [coeffH1Mk_eq_zero_iff] at this
      exact this
    rw [mem_coeffCoboundaries_iff] at hcob
    obtain ⟨v₀, hv₀⟩ := hcob

    rw [heckeH1_mk, ← sub_eq_zero, ← map_smul, ← map_sub, coeffH1Mk_eq_zero_iff, mem_coeffCoboundaries_iff]
    refine ⟨j v₀, funext fun g => ?_⟩
    have := congrFun hv₀ g
    simp only [Pi.sub_apply, Pi.smul_apply] at this
    symm
    show coeffHeckeFun N ℓ ρ (a ℓ) (fun g => j ((z₀ : Gamma0 N → V₀) g)) g - i (lam ℓ) • j ((z₀ : Gamma0 N → V₀) g) =
      ρ g (j v₀) - j v₀
    rw [← carry_coeffHeckeFun i N ρ₀ ρ j hj ℓ (a₀ ℓ) (a ℓ) (fun v => hja ℓ v hℓ hℓN hℓS), ← hw₀, ← hj,
      ← LinearMap.map_smulₛₗ, ← map_sub, ← this, map_sub]

end Main

end BCChi
p2m_reactivate "P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange.BCChi"

theorem solution
    (N : ℕ) {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (S₀ : Set ℕ)
    {V₀ V : Type} [AddCommGroup V₀] [Module K₀ V₀] [AddCommGroup V] [Module K V]
    (ρ₀ : Representation K₀ (CongruenceSubgroup.Gamma0 N) V₀) (ρ : Representation K (CongruenceSubgroup.Gamma0 N) V)
    (a₀ : ℕ → (V₀ →ₗ[K₀] V₀)) (a : ℕ → (V →ₗ[K] V))
    (ha : ∀ (ℓ : ℕ) [NeZero ℓ], ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ →
      ∀ u : ↥(HeckeEis.heckeUpper N ℓ),
        a ℓ ∘ₗ ρ (HeckeEis.heckeConj N ℓ u) = ρ (u : CongruenceSubgroup.Gamma0 N) ∘ₗ a ℓ)
    (j : V₀ →ₛₗ[i] V) (hj : ∀ (g : CongruenceSubgroup.Gamma0 N) (v : V₀), j (ρ₀ g v) = ρ g (j v))
    (hja : ∀ (ℓ : ℕ) (v : V₀), ℓ.Prime → ¬ ℓ ∣ N → ℓ ∉ S₀ → j (a₀ ℓ v) = a ℓ (j v))
    (hbc : ∃ (ι : Type) (b₀ : Module.Basis ι K₀ V₀) (b : Module.Basis ι K V), ∀ s : ι, b s = j (b₀ s))
    (lam : ℕ → K₀) (h : HeckeEis.IsEigensystemH1 N ρ₀ a₀ S₀ lam) :
    HeckeEis.IsEigensystemH1 N ρ a S₀ (fun ℓ => i (lam ℓ)) :=
  BCChi.main N i S₀ ρ₀ ρ a₀ a ha j hj hja hbc lam h

end S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange
end P2MW
export P2MW.S_HeckeEis_isEigensystemH1_of_isEigensystemH1_of_isBaseChange (solution)
