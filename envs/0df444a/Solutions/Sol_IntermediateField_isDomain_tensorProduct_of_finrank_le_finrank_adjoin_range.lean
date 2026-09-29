-- Prove2me | solution 1 for IntermediateField.isDomain_tensorProduct_of_finrank_le_finrank_adjoin_range
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/661b1806-78e6-50a1-a54b-1f02fc591661

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IntermediateField_isDomain_tensorProduct_of_finrank_le_finrank_adjoin_range
set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

open scoped TensorProduct Polynomial
open IntermediateField

universe u

noncomputable section

namespace DBTensor

variable {𝔽 : Type u} [Field 𝔽] {k : Type u} [Field k] [Algebra 𝔽 k]
  {κ : Type u} [Field κ] [Algebra 𝔽 κ] [Algebra 𝔽[X] κ] [IsScalarTower 𝔽 𝔽[X] κ]
  {Ω : Type u} [Field Ω] [Algebra k Ω] [Algebra 𝔽 Ω] [IsScalarTower 𝔽 k Ω]
  (ρ : κ →ₐ[𝔽] Ω)

theorem rho_mem_adjoin (c : ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ))) :
    ρ (c : κ) ∈ IntermediateField.adjoin k ({ρ (algebraMap 𝔽[X] κ Polynomial.X)} : Set Ω) := by
  have h1 : ρ (c : κ) ∈ (IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)).map ρ := ⟨c, c.2, rfl⟩
  rw [IntermediateField.adjoin_map, Set.image_singleton] at h1
  exact (IntermediateField.adjoin_le_iff (T := (IntermediateField.adjoin k
    ({ρ (algebraMap 𝔽[X] κ Polynomial.X)} : Set Ω)).restrictScalars 𝔽)).mpr
      (by simpa using IntermediateField.mem_adjoin_simple_self k (ρ (algebraMap 𝔽[X] κ Polynomial.X))) h1

theorem linearIndependent_pow_of_transcendental {t : Ω} (htr : Transcendental k t) :
    LinearIndependent k (fun n : ℕ => t ^ n) := by
  rw [linearIndependent_iff]
  intro l hl
  have hinj := transcendental_iff_injective.mp htr
  have h0 : Polynomial.aeval t (Polynomial.ofFinsupp (.ofCoeff l)) = 0 := by
    rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
    convert hl using 1
    refine Finset.sum_congr (by rfl) fun n _ => ?_
    rw [Algebra.smul_def]
    rfl
  have := hinj (a₁ := Polynomial.ofFinsupp (.ofCoeff l)) (a₂ := 0) (by rw [h0, map_zero])
  exact AddMonoidAlgebra.ofCoeff_eq_zero.mp (Polynomial.ofFinsupp_eq_zero.mp this)

theorem linearIndependent_adjoin_of_transcendental {t : Ω} (htr : Transcendental k t)
    {ιa : Type*} {a : ιa → k} (ha : LinearIndependent 𝔽 a) :
    LinearIndependent ↥(Algebra.adjoin 𝔽 ({t} : Set Ω)) (fun i => algebraMap k Ω (a i)) := by
  classical

  have hsmul : LinearIndependent 𝔽 (fun p : ιa × ℕ => a p.1 • t ^ p.2) :=
    linearIndependent_smul (R := 𝔽) (S := k) (A := Ω) ha (linearIndependent_pow_of_transcendental htr)
  rw [linearIndependent_iff']
  intro s g hg i hi

  have hP : ∀ j, ∃ P : 𝔽[X], Polynomial.aeval t P = (g j : Ω) := fun j =>
    (AlgHom.mem_range _).mp ((le_of_eq (Algebra.adjoin_singleton_eq_range_aeval 𝔽 t)) (g j).2)
  choose P hP using hP

  let T : Finset ℕ := s.biUnion fun j => (P j).support
  have hT : ∀ j ∈ s, (P j).support ⊆ T := fun j hj => Finset.subset_biUnion_of_mem (fun j => (P j).support) hj

  have heval : ∀ j ∈ s, (g j : Ω) = ∑ n ∈ T, algebraMap 𝔽 Ω ((P j).coeff n) * t ^ n := fun j hj => by
    rw [← hP j, Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def]
    exact Finset.sum_subset (hT j hj) fun n _ hn => by
      rw [Polynomial.notMem_support_iff.mp hn, map_zero, zero_mul]

  have hrel : ∑ p ∈ s ×ˢ T, ((P p.1).coeff p.2) • (a p.1 • t ^ p.2) = 0 := by
    rw [Finset.sum_product, ← hg]
    refine Finset.sum_congr rfl fun j hj => ?_
    have : (g j • algebraMap k Ω (a j) : Ω) = (g j : Ω) * algebraMap k Ω (a j) := rfl
    rw [this, heval j hj, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Algebra.smul_def, Algebra.smul_def]
    ring
  have hcoeff := linearIndependent_iff'.mp hsmul (s ×ˢ T) (fun p => (P p.1).coeff p.2) hrel

  have hPi : P i = 0 := by
    ext n
    rw [Polynomial.coeff_zero]
    by_cases hn : n ∈ (P i).support
    · exact hcoeff (i, n) (Finset.mk_mem_product hi (hT i hi hn))
    · exact Polynomial.notMem_support_iff.mp hn
  apply Subtype.ext
  simp only [← hP i, hPi, map_zero, ZeroMemClass.coe_zero]

theorem linearIndependent_rho_of_transcendental
    (htr : Transcendental k (ρ (algebraMap 𝔽[X] κ Polynomial.X)))
    {ιe : Type*} (e : Module.Basis ιe 𝔽 ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ))) :
    LinearIndependent k (fun i : ιe => ρ (e i : κ)) := by
  classical
  set t : Ω := ρ (algebraMap 𝔽[X] κ Polynomial.X) with ht

  let fa : k →ₐ[𝔽] Ω := IsScalarTower.toAlgHom 𝔽 k Ω
  let A : IntermediateField 𝔽 Ω := fa.fieldRange
  let L₁ : IntermediateField 𝔽 Ω := IntermediateField.adjoin 𝔽 ({t} : Set Ω)

  let ak := Module.Free.chooseBasis 𝔽 k
  let aA : Module.Basis _ 𝔽 ↥A := ak.map (AlgEquiv.ofInjectiveField fa).toLinearEquiv

  have hR : LinearIndependent ↥(Algebra.adjoin 𝔽 ({t} : Set Ω)) (A.val ∘ aA) := by
    convert linearIndependent_adjoin_of_transcendental htr ak.linearIndependent using 2 with i
    rfl
  have hL : LinearIndependent ↥L₁ (A.val ∘ aA) := by
    open IntermediateField.algebraAdjoinAdjoin in
    exact (LinearIndependent.iff_fractionRing ↥(Algebra.adjoin 𝔽 ({t} : Set Ω)) ↥L₁).mp hR
  have LD : A.LinearDisjoint ↥L₁ := IntermediateField.LinearDisjoint.of_basis_left aA hL

  have hmem : ∀ i, ρ (e i : κ) ∈ L₁ := fun i => by
    have h1 : ρ (e i : κ) ∈ (IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)).map ρ :=
      ⟨e i, (e i).2, rfl⟩
    rwa [IntermediateField.adjoin_map, Set.image_singleton] at h1
  let bL : ιe → ↥L₁ := fun i => ⟨ρ (e i : κ), hmem i⟩
  have hbL : LinearIndependent 𝔽 bL := by
    refine LinearIndependent.of_comp (L₁.val.toLinearMap) ?_
    have : LinearIndependent 𝔽 (fun i => ρ (e i : κ)) :=
      (e.linearIndependent.map' ((ρ.toLinearMap).comp
        (IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)).val.toLinearMap)
        (LinearMap.ker_eq_bot.mpr ((ρ.injective).comp Subtype.val_injective)))
    exact this
  have hA : LinearIndependent ↥A (algebraMap ↥L₁ Ω ∘ bL) := LD.linearIndependent_right' hbL

  have hk : LinearIndependent k (algebraMap ↥L₁ Ω ∘ bL) :=
    hA.map_of_injective_injective (AlgEquiv.ofInjectiveField fa) (AddMonoidHom.id Ω)
      (fun r hr => (AlgEquiv.ofInjectiveField fa).injective (hr.trans (map_zero _).symm)) (fun m hm => hm)
      (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)
  exact hk

theorem linearIndependent_rho_basis
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ)
    (htr : Transcendental k (ρ (algebraMap 𝔽[X] κ Polynomial.X)))
    (hdeg : Module.finrank ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ ≤
      Module.finrank ↥(IntermediateField.adjoin k ({⟨ρ (algebraMap 𝔽[X] κ Polynomial.X),
          IntermediateField.subset_adjoin k (Set.range ρ) ⟨_, rfl⟩⟩} : Set ↥(IntermediateField.adjoin k (Set.range ρ))))
        ↥(IntermediateField.adjoin k (Set.range ρ)))
    {ιy : Type*} [Fintype ιy]
    (y : Module.Basis ιy ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ) :
    LinearIndependent ↥(IntermediateField.adjoin k ({ρ (algebraMap 𝔽[X] κ Polynomial.X)} : Set Ω))
      (fun j : ιy => ρ (y j)) := by
  classical
  haveI := hfin
  let x : κ := algebraMap 𝔽[X] κ Polynomial.X
  let t : Ω := ρ x
  let L₀ : IntermediateField 𝔽 κ := IntermediateField.adjoin 𝔽 ({x} : Set κ)
  let Kt : IntermediateField k Ω := IntermediateField.adjoin k ({t} : Set Ω)
  let E : IntermediateField k Ω := IntermediateField.adjoin k (Set.range ρ)
  have htE : t ∈ E := IntermediateField.subset_adjoin k (Set.range ρ) ⟨_, rfl⟩
  let tE : ↥E := ⟨t, htE⟩
  let K'' : IntermediateField k ↥E := IntermediateField.adjoin k ({tE} : Set ↥E)
  have hKtE : Kt ≤ E := IntermediateField.adjoin_simple_le_iff.mpr htE
  let M := ↥(IntermediateField.extendScalars hKtE)

  let S : Submodule ↥Kt Ω := Submodule.span ↥Kt (Set.range fun j => ρ (y j))

  have hA1 : ∀ z : κ, ρ z ∈ S := fun z => by
    rw [← y.linearCombination_repr z, Finsupp.linearCombination_apply, map_finsuppSum]
    refine Submodule.sum_mem _ fun j _ => ?_
    have : ρ ((y.repr z j) • y j) = (⟨ρ (y.repr z j : κ), rho_mem_adjoin ρ _⟩ : ↥Kt) • ρ (y j) := by
      change ρ ((y.repr z j : κ) * y j) = ρ (y.repr z j : κ) * ρ (y j)
      rw [map_mul]
    show ρ ((y.repr z j) • y j) ∈ S
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

  let φ : ↥L₀ →+* ↥Kt := (ρ.toRingHom.comp (algebraMap ↥L₀ κ)).codRestrict Kt fun c => rho_mem_adjoin ρ c
  have hφ : (algebraMap ↥Kt Ω).comp φ = ρ.toRingHom.comp (algebraMap ↥L₀ κ) := RingHom.ext fun c => rfl
  have halg : ∀ w ∈ Set.range ρ, IsAlgebraic ↥Kt w := by
    rintro _ ⟨z, rfl⟩
    have hz : IsIntegral ↥L₀ z := Algebra.IsIntegral.isIntegral z
    refine IsIntegral.isAlgebraic ⟨(minpoly ↥L₀ z).map φ, (minpoly.monic hz).map φ, ?_⟩
    rw [Polynomial.eval₂_map, hφ]
    have h := Polynomial.hom_eval₂ (minpoly ↥L₀ z) (algebraMap ↥L₀ κ) ρ.toRingHom z
    rw [← Polynomial.aeval_def, minpoly.aeval, map_zero] at h
    exact h.symm

  have hA2 : ∀ w ∈ (E : Set Ω), w ∈ S := by
    intro w hw
    have h1 : E ≤ (IntermediateField.adjoin ↥Kt (Set.range ρ)).restrictScalars k :=
      IntermediateField.adjoin_le_iff.mpr (IntermediateField.subset_adjoin ↥Kt (Set.range ρ))
    have h2 : w ∈ (IntermediateField.adjoin ↥Kt (Set.range ρ)).toSubalgebra := h1 hw
    rw [IntermediateField.adjoin_toSubalgebra_of_isAlgebraic halg] at h2
    have h3 : w ∈ Subalgebra.toSubmodule (Algebra.adjoin ↥Kt (Set.range ρ)) := h2
    rw [Algebra.adjoin_eq_span] at h3
    have h4 : Submodule.span ↥Kt (Submonoid.closure (Set.range ρ) : Set Ω) ≤ S := by
      rw [Submodule.span_le]
      intro w hw
      have hw' : w ∈ MonoidHom.mrange ρ.toRingHom.toMonoidHom :=
        (Submonoid.closure_le.mpr fun _ h => h) hw
      obtain ⟨z, rfl⟩ := MonoidHom.mem_mrange.mp hw'
      exact hA1 z
    exact h4 h3

  let σ' : ↥K'' ≃+* ↥Kt :=
    ((IntermediateField.liftAlgEquiv K'').trans (IntermediateField.equivOfEq (IntermediateField.lift_adjoin_simple k E tE))).toRingEquiv
  let jE : ↥E ≃+* M :=
    { toFun := fun v => ⟨v.1, v.2⟩
      invFun := fun v => ⟨v.1, v.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl }
  have hc : (algebraMap ↥Kt M).comp σ'.toRingHom = jE.toRingHom.comp (algebraMap ↥K'' ↥E) :=
    RingHom.ext fun c => Subtype.ext rfl
  have hfinrank : Module.finrank ↥K'' ↥E = Module.finrank ↥Kt M := Algebra.finrank_eq_of_equiv_equiv σ' jE hc

  let yM : ιy → M := fun j => ⟨ρ (y j), (IntermediateField.subset_adjoin k (Set.range ρ) ⟨_, rfl⟩ : ρ (y j) ∈ E)⟩
  have hval : Function.Injective (IntermediateField.extendScalars hKtE).val.toLinearMap := Subtype.val_injective
  have hspan : ⊤ ≤ Submodule.span ↥Kt (Set.range yM) := by
    intro v _
    rw [← Submodule.apply_mem_span_image_iff_mem_span hval, ← Set.range_comp]
    exact hA2 v.1 v.2
  have hcard : Fintype.card ιy = Module.finrank ↥Kt M := by
    apply le_antisymm
    · rw [← hfinrank, ← Module.finrank_eq_card_basis y]
      exact hdeg
    · have h := finrank_range_le_card (R := ↥Kt) yM
      have hs : Submodule.span ↥Kt (Set.range yM) = ⊤ := eq_top_iff.mpr hspan
      simp only [Set.finrank] at h
      rw [hs, finrank_top] at h
      exact h
  have hind : LinearIndependent ↥Kt yM := linearIndependent_of_top_le_span_of_card_eq_finrank hspan hcard
  exact hind.map' (IntermediateField.extendScalars hKtE).val.toLinearMap (LinearMap.ker_eq_bot.mpr hval)

theorem linearIndependent_smulTower
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ)
    (htr : Transcendental k (ρ (algebraMap 𝔽[X] κ Polynomial.X)))
    (hdeg : Module.finrank ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ ≤
      Module.finrank ↥(IntermediateField.adjoin k ({⟨ρ (algebraMap 𝔽[X] κ Polynomial.X),
          IntermediateField.subset_adjoin k (Set.range ρ) ⟨_, rfl⟩⟩} : Set ↥(IntermediateField.adjoin k (Set.range ρ))))
        ↥(IntermediateField.adjoin k (Set.range ρ)))
    {ιe : Type*} (e : Module.Basis ιe 𝔽 ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)))
    {ιy : Type*} [Fintype ιy]
    (y : Module.Basis ιy ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ) :
    LinearIndependent k (fun p : ιe × ιy => ρ (e p.1 • y p.2)) := by

  let bS : ιe → ↥(IntermediateField.adjoin k ({ρ (algebraMap 𝔽[X] κ Polynomial.X)} : Set Ω)) :=
    fun i => ⟨ρ (e i : κ), rho_mem_adjoin ρ (e i)⟩
  have hb : LinearIndependent k bS := by
    refine LinearIndependent.of_comp
      ((IntermediateField.adjoin k ({ρ (algebraMap 𝔽[X] κ Polynomial.X)} : Set Ω)).val.toLinearMap) ?_
    exact linearIndependent_rho_of_transcendental ρ htr e
  have hc := linearIndependent_rho_basis ρ hfin htr hdeg y
  have h := linearIndependent_smul hb hc
  convert h using 2 with p
  change ρ ((e p.1 : κ) * y p.2) = ρ (e p.1 : κ) * ρ (y p.2)
  rw [map_mul]

end DBTensor

open DBTensor in

theorem solution
    (𝔽 : Type u) [Field 𝔽] (k : Type u) [Field k] [Algebra 𝔽 k]
    (κ : Type u) [Field κ] [Algebra 𝔽 κ] [Algebra 𝔽[X] κ] [IsScalarTower 𝔽 𝔽[X] κ]
    (hfin : FiniteDimensional ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ)
    (Ω : Type u) [Field Ω] [Algebra k Ω] [Algebra 𝔽 Ω] [IsScalarTower 𝔽 k Ω]
    (ρ : κ →ₐ[𝔽] Ω) (htr : Transcendental k (ρ (algebraMap 𝔽[X] κ Polynomial.X)))
    (hdeg : Module.finrank ↥(IntermediateField.adjoin 𝔽 ({algebraMap 𝔽[X] κ Polynomial.X} : Set κ)) κ ≤
      Module.finrank ↥(IntermediateField.adjoin k ({⟨ρ (algebraMap 𝔽[X] κ Polynomial.X),
          IntermediateField.subset_adjoin k (Set.range ρ) ⟨_, rfl⟩⟩} : Set ↥(IntermediateField.adjoin k (Set.range ρ))))
        ↥(IntermediateField.adjoin k (Set.range ρ))) :
    IsDomain (k ⊗[𝔽] κ) := by
  classical
  set x : κ := algebraMap 𝔽[X] κ Polynomial.X with hx
  let L₀ : IntermediateField 𝔽 κ := IntermediateField.adjoin 𝔽 ({x} : Set κ)
  haveI : FiniteDimensional ↥L₀ κ := hfin

  let e := Module.Free.chooseBasis 𝔽 ↥L₀
  let y := Module.finBasis ↥L₀ κ
  let bκ : Module.Basis (_ × Fin (Module.finrank ↥L₀ κ)) 𝔽 κ := e.smulTower y

  let fa : k →ₐ[𝔽] Ω := IsScalarTower.toAlgHom 𝔽 k Ω
  have hfa : Function.Injective fa := (algebraMap k Ω).injective

  have hind : LinearIndependent k (fun p => ρ (bκ p)) := by
    have := DBTensor.linearIndependent_smulTower ρ hfin htr hdeg e y
    convert this using 2 with p
    rw [Module.Basis.smulTower_apply]

  have hind' : LinearIndependent ↥fa.range (ρ.range.val ∘ (bκ.map (AlgEquiv.ofInjective ρ ρ.injective).toLinearEquiv)) := by
    have h2 : LinearIndependent ↥fa.range (fun p => ρ (bκ p)) :=
      hind.map_of_surjective_injective (AlgEquiv.ofInjectiveField fa) (AddMonoidHom.id Ω)
        (AlgEquiv.surjective _) (by simp) (fun _ _ => by simp_rw [Algebra.smul_def]; rfl)
    convert h2 using 1
    rfl
  have H : fa.range.LinearDisjoint ρ.range :=
    Subalgebra.LinearDisjoint.of_basis_right _ _ (bκ.map (AlgEquiv.ofInjective ρ ρ.injective).toLinearEquiv) hind'
  exact H.isDomain_of_injective hfa ρ.injective

end

end S_IntermediateField_isDomain_tensorProduct_of_finrank_le_finrank_adjoin_range
end P2MW
export P2MW.S_IntermediateField_isDomain_tensorProduct_of_finrank_le_finrank_adjoin_range (solution)
