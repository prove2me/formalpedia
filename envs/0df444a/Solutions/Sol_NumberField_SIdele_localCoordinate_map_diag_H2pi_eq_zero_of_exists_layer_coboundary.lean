-- Prove2me | solution 1 for NumberField.SIdele.localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/c58220e6-5bc8-52fb-bee1-65b7b9de46cb

import Mathlib
import Definitions.Def_NumberField_PlaceAbove
import Definitions.Def_NumberField_PlaceDecompositionAction
import Definitions.Def_NumberField_SIdeleModule
import Definitions.Def_DedekindDomain_Completion_BaseChange
import Definitions.Def_GaloisRep_CompletionBridge
import Theorems.Thm_NumberField_PlaceDecomp_exists_fundamentalClass_units_adicCompletion
import Theorems.Thm_NumberField_PlaceDecomp_exists_restrict_decomp_surjective_of_tower
import Theorems.Thm_NumberField_PlaceDecomp_forall_smul_eq_iff_mem_range_adicCompletionSemialgHom
import Theorems.Thm_groupCohomology_H2inf_injective_of_subsingleton_H1_res
import Theorems.Thm_groupCohomology_coindIso_hom_eq_map_subtype_comp_map_eval_one
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

p2m_attr_erase "ext" "IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext"
namespace P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary
p2m_attr_erase "instance" "ExtCitation.levelSubgroup_normal ExtCitation.levelSubgroup_finiteIndex ExtCitation.inertiaPullback_normal"
p2m_attr_erase "simp" "IsLocalRing.principalUnits_zero groupCohomology.Cores.Transversal.mk.sizeOf_spec groupCohomology.Cores.Transversal.mk.injEq"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

section

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary.NumberField CategoryTheory groupCohomology P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary.groupCohomology"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary.NumberField.PlaceDecomp"

universe u

namespace groupCohomology
p2m_export "groupCohomology" "H2π congr coindIso cocycles₂ d₁₂_hom_apply coe_mapCocycles₂ H2π_comp_map_apply map mem_cocycles₂_iff mapCocycles₂ H2π_eq_zero_iff H1 cochainsMap₂ H2inf_injective_of_subsingleton_H1_res coindIso_hom_eq_map_subtype_comp_map_eval_one"
p2m_open "groupCohomology"

private theorem H2π_quotientToInvariants_eq_zero_of_forall_eq_sub_add
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (N : Subgroup G) [N.Normal]
    [Subsingleton (H1 (Rep.res N.subtype A))]
    (f : cocycles₂ (A.quotientToInvariants N)) (y : G → A)
    (hy : ∀ g h : G,
      ((f ((g : G ⧸ N), (h : G ⧸ N)) : A.quotientToInvariants N) : A) = A.ρ g (y h) - y (g * h) + y g) :
    H2π (A.quotientToInvariants N) f = 0 := by
  apply H2inf_injective_of_subsingleton_H1_res A N
  rw [map_zero, H2π_comp_map_apply, H2π_eq_zero_iff]
  refine ⟨y, ?_⟩
  funext gh
  obtain ⟨g, h⟩ := gh
  have := hy g h
  first
    | simpa [coe_mapCocycles₂, cochainsMap₂] using this.symm
    | (simp [coe_mapCocycles₂, cochainsMap₂] at this ⊢; exact this.symm)
    | exact this.symm

private theorem H2π_eq_zero_of_surjective_of_forall_eq_sub_add
    {k G D : Type u} [CommRing k] [Group G] [Group D] (r : G →* D) (hr : Function.Surjective r)
    (A : Rep k G) [Subsingleton (H1 (Rep.res r.ker.subtype A))]
    (B : Rep k D) (j : B →ₗ[k] A) (hj : Function.Injective j)
    (hjρ : ∀ (g : G) (b : B), j (B.ρ (r g) b) = A.ρ g (j b))
    (hjinv : ∀ a : A, (∀ n : G, n ∈ r.ker → A.ρ n a = a) → ∃ b : B, j b = a)
    (f : cocycles₂ B) (y : G → A)
    (hy : ∀ g h : G, j (f (r g, r h)) = A.ρ g (y h) - y (g * h) + y g) :
    H2π B f = 0 := by
  set N : Subgroup G := r.ker with hN
  let e : G ⧸ N ≃* D := QuotientGroup.quotientKerEquivOfSurjective r hr
  have he : ∀ g : G, e (g : G ⧸ N) = r g := fun g => QuotientGroup.kerLift_mk r g

  have hinv : ∀ b : B, j b ∈ Representation.invariants (A.ρ.comp N.subtype) := by
    intro b
    rw [Representation.mem_invariants]
    rintro ⟨n, hn⟩
    have h1 : r n = 1 := hn
    simpa [h1] using (hjρ n b).symm

  let F : (G ⧸ N) × (G ⧸ N) → A.quotientToInvariants N := fun x => ⟨j (f (e x.1, e x.2)), hinv _⟩
  have hFρ : ∀ (g : G) (s : A.quotientToInvariants N),
      (((A.quotientToInvariants N).ρ (g : G ⧸ N) s : A.quotientToInvariants N) : A) = A.ρ g (s : A) := fun _ _ => rfl
  have hFmem : F ∈ cocycles₂ (A.quotientToInvariants N) := by
    rw [mem_cocycles₂_iff]
    intro x z w
    induction x using QuotientGroup.induction_on with
    | H g =>
      apply Subtype.ext
      have hf := (mem_cocycles₂_iff (A := B) f).1 f.2 (r g) (e z) (e w)
      simp only [F, Submodule.coe_add, hFρ, map_mul, he]
      rw [← hjρ]
      simpa only [map_add] using congrArg j hf
  let Ft : cocycles₂ (A.quotientToInvariants N) := ⟨F, hFmem⟩
  have hFt : H2π (A.quotientToInvariants N) Ft = 0 := by
    apply H2π_quotientToInvariants_eq_zero_of_forall_eq_sub_add A N Ft y
    intro g h
    change j (f (e ↑g, e ↑h)) = _
    simpa [he] using hy g h
  rw [H2π_eq_zero_iff] at hFt
  obtain ⟨u, hu⟩ := hFt

  have hlift : ∀ d : D, ∃ b : B, j b = ((u (e.symm d) : A.quotientToInvariants N) : A) := by
    intro d
    apply hjinv
    intro n hn
    exact (Representation.mem_invariants _ _).1 (u (e.symm d)).2 ⟨n, hn⟩
  choose v hv using hlift
  rw [H2π_eq_zero_iff]
  refine ⟨v, ?_⟩
  funext dd
  obtain ⟨d₁, d₂⟩ := dd
  obtain ⟨g₁, rfl⟩ := hr d₁
  obtain ⟨g₂, rfl⟩ := hr d₂
  have hs₁ : e.symm (r g₁) = (g₁ : G ⧸ N) := e.symm_apply_eq.2 (he g₁).symm
  have hs₂ : e.symm (r g₂) = (g₂ : G ⧸ N) := e.symm_apply_eq.2 (he g₂).symm
  have hs₁₂ : e.symm (r g₁ * r g₂) = ((g₁ * g₂ : G) : G ⧸ N) := by
    rw [map_mul, hs₁, hs₂]; rfl
  apply hj
  have hu' := congrFun hu ((g₁ : G ⧸ N), (g₂ : G ⧸ N))
  have hu'' := congrArg (fun s : A.quotientToInvariants N => (s : A)) hu'
  simp only [d₁₂_hom_apply, Submodule.coe_add, Submodule.coe_sub, hFρ] at hu''
  simp only [d₁₂_hom_apply, map_add, map_sub, hjρ, hv, hs₁, hs₂, hs₁₂]
  exact hu''

end groupCohomology

namespace NumberField
p2m_export "NumberField" "place PlaceAbove.above PlaceDecomp.decomp SIdele.fibre SIdele.diag SUnits.diagIn SUnits.diagIn_hom_apply_apply FiniteSIdele.D FiniteSIdele.localUnits SUnits.sUnitsRep SUnits.loc SUnits.val PlaceDecomp.exists_fundamentalClass_units_adicCompletion PlaceDecomp.exists_restrict_decomp_surjective_of_tower PlaceDecomp.forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
namespace PlaceDecomp
p2m_export "NumberField.PlaceDecomp" "decomp actRingEquiv_apply smul_def coe_smul_units exists_fundamentalClass_units_adicCompletion exists_restrict_decomp_surjective_of_tower forall_smul_eq_iff_mem_range_adicCompletionSemialgHom"
p2m_open "NumberField.PlaceDecomp NumberField"

variable (E K K'' : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Field K''] [NumberField K'']
  [Algebra E K] [Algebra K K''] [Algebra E K''] [IsScalarTower E K K''] [IsGalois E K''] [IsGalois E K]
  (w'' : HeightOneSpectrum (𝓞 K''))

omit [NumberField E] [NumberField K] [IsGalois E K''] [IsGalois E K] in

private theorem smul_eq_smul_of_coe_eq (τ : decomp K K'' w'') (σ : decomp E K'' w'')
    (h : (σ : K'' ≃ₐ[E] K'') = AlgEquiv.restrictScalars E (τ : K'' ≃ₐ[K] K'')) (x : w''.adicCompletion K'') :
    τ • x = σ • x := by
  rw [smul_def, smul_def]
  apply IsDedekindDomain.HeightOneSpectrum.adicCompletion.ext
  rw [actRingEquiv_apply, actRingEquiv_apply, h]
  rfl

private theorem H2π_eq_zero_of_exists_coboundary_above (p : HeightOneSpectrum (𝓞 K))
    (hp : HeightOneSpectrum.under (𝓞 K) w'' = p)
    (F : cocycles₂ (Rep.ofMulDistribMulAction (decomp E K p) (p.adicCompletion K)ˣ))
    (y : decomp E K'' w'' → Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ)
    (hy : ∀ (g h : decomp E K'' w'') (a b : decomp E K p),
      (a : K ≃ₐ[E] K) = AlgEquiv.restrictNormalHom K (g : K'' ≃ₐ[E] K'') →
      (b : K ≃ₐ[E] K) = AlgEquiv.restrictNormalHom K (h : K'' ≃ₐ[E] K'') →
      Additive.ofMul (Units.map (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
          (⟨w'', hp⟩ : p.Extension (𝓞 K''))).toRingHom.toMonoidHom (Additive.toMul (F (a, b)))) =
        (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) - y (g * h) + y g) :
    H2π _ F = 0 := by
  subst hp
  obtain ⟨r, hr, hrcoe, -, hlift, hsemi⟩ := exists_restrict_decomp_surjective_of_tower E K K'' w''
  haveI : IsGalois K K'' := IsGalois.tower_top_of_isGalois E K K''
  set ι : (HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K →+* w''.adicCompletion K'' :=
    (HeightOneSpectrum.Extension.adicCompletionSemialgHom K K''
      (⟨w'', rfl⟩ : (HeightOneSpectrum.under (𝓞 K) w'').Extension (𝓞 K''))).toRingHom with hιdef

  haveI : Subsingleton (H1 (Rep.res r.ker.subtype
      (Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ))) := by
    obtain ⟨-, hH1, -, -⟩ := exists_fundamentalClass_units_adicCompletion E K'' w''
    exact ModuleCat.subsingleton_of_isZero (hH1 r.ker)

  let j : Rep.ofMulDistribMulAction (decomp E K (HeightOneSpectrum.under (𝓞 K) w''))
        ((HeightOneSpectrum.under (𝓞 K) w'').adicCompletion K)ˣ →ₗ[ℤ]
      Rep.ofMulDistribMulAction (decomp E K'' w'') (w''.adicCompletion K'')ˣ :=
    (MonoidHom.toAdditive (Units.map ι.toMonoidHom)).toIntLinearMap
  have hj : Function.Injective j := fun u₁ u₂ h =>
    Additive.toMul.injective (Units.map_injective ι.injective (congrArg Additive.toMul h))
  refine groupCohomology.H2π_eq_zero_of_surjective_of_forall_eq_sub_add r hr _ _ j hj ?_ ?_ F y ?_
  · intro σ b
    apply Additive.toMul.injective
    apply Units.ext
    simp only [j, Rep.ofMulDistribMulAction_ρ_apply_apply, RingHom.toMonoidHom_eq_coe]
    exact hsemi σ _
  · intro a ha
    obtain ⟨z, hz⟩ := (forall_smul_eq_iff_mem_range_adicCompletionSemialgHom K K'' w''
        ((Additive.toMul a : (w''.adicCompletion K'')ˣ) : w''.adicCompletion K'')).1 (fun τ => by
      obtain ⟨σ, hσ, hσ1⟩ := hlift τ
      have h1 := ha σ hσ1
      have h2 := congrArg (fun t => ((Additive.toMul t : (w''.adicCompletion K'')ˣ) : w''.adicCompletion K'')) h1
      simp only [Rep.ofMulDistribMulAction_ρ_apply_apply, toMul_ofMul, coe_smul_units] at h2
      rw [smul_eq_smul_of_coe_eq E K K'' w'' τ σ hσ]
      exact h2)
    have hz0 : z ≠ 0 := by
      rintro rfl
      exact (Additive.toMul a).ne_zero (by simpa using hz.symm)
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    apply Units.ext
    first
      | simpa [j, AddMonoidHom.coe_toIntLinearMap, MonoidHom.toAdditive_apply_apply, Units.coe_map, toMul_ofMul, Units.val_mk0] using hz
      | (simp [j]; exact hz)
  · intro g h
    exact hy g h (r g) (r h) (hrcoe g) (hrcoe h)

end NumberField.PlaceDecomp

end

p2m_open "IsDedekindDomain NumberField P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary.NumberField CategoryTheory groupCohomology P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary.groupCohomology"
p2m_open_scoped "NumberField.PlaceDecomp P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary.NumberField.PlaceDecomp"

theorem solution
    (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K] [Algebra E K] [IsGalois E K]
    (S : Finset (HeightOneSpectrum (𝓞 E))) (f : cocycles₂ (SUnits.sUnitsRep E K S)) (v : {v // v ∈ S})
    (hloc : ∃ (K'' : Type) (_ : Field K'') (_ : NumberField K'') (_ : Algebra E K'') (_ : Algebra K K'')
      (_ : IsScalarTower E K K'') (_ : IsGalois E K'') (w'' : HeightOneSpectrum (𝓞 K''))
      (_ : HeightOneSpectrum.under (𝓞 K) w'' = PlaceAbove.above E K v.1)
      (y : PlaceDecomp.decomp E K'' w'' →
        Rep.ofMulDistribMulAction (PlaceDecomp.decomp E K'' w'') (w''.adicCompletion K'')ˣ),
      ∀ g h : PlaceDecomp.decomp E K'' w'',
        Additive.ofMul (Units.map (algebraMap K'' (w''.adicCompletion K'')).toMonoidHom
            (Units.map (algebraMap K K'').toMonoidHom (SUnits.val E K S
              (f (AlgEquiv.restrictNormalHom K (g : K'' ≃ₐ[E] K''),
                  AlgEquiv.restrictNormalHom K (h : K'' ≃ₐ[E] K'')))))) =
          (Rep.ofMulDistribMulAction (PlaceDecomp.decomp E K'' w'') (w''.adicCompletion K'')ˣ).ρ g (y h) -
            y (g * h) + y g) :
    (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) 2 ≫
      (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) 2).hom).hom
      ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) (NumberField.SIdele.diag E K S) 2).hom
        (H2π (SUnits.sUnitsRep E K S) f)) = 0 := by
  classical
  obtain ⟨K'', _, _, _, _, _, _, w'', hw'', y, hy⟩ := hloc

  let ev : Rep.res (FiniteSIdele.D E K v.1).subtype
      (Rep.coind (FiniteSIdele.D E K v.1).subtype (FiniteSIdele.localUnits E K v.1)) ⟶
        FiniteSIdele.localUnits E K v.1 :=
    (Rep.resCoindHomEquiv (FiniteSIdele.D E K v.1).subtype _ (FiniteSIdele.localUnits E K v.1)).symm (𝟙 _)
  have hev : ∀ x, ev.hom x = (x : (K ≃ₐ[E] K) → FiniteSIdele.localUnits E K v.1) 1 := fun _ => rfl

  let F : cocycles₂ (FiniteSIdele.localUnits E K v.1) :=
    mapCocycles₂ (MonoidHom.id _) ev (mapCocycles₂ (FiniteSIdele.D E K v.1).subtype (𝟙 _)
      (mapCocycles₂ (MonoidHom.id _) (GroupCohomology.RepPi.proj (SIdele.fibre E K S) (Sum.inl (Sum.inl v)))
        (mapCocycles₂ (MonoidHom.id _) (SIdele.diag E K S) f)))

  have hcoord : (groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K))
        (GroupCohomology.RepPi.proj (NumberField.SIdele.fibre E K S) (Sum.inl (Sum.inl v))) 2 ≫
      (groupCohomology.coindIso (NumberField.FiniteSIdele.localUnits E K v.1) 2).hom).hom
      ((groupCohomology.map (MonoidHom.id (K ≃ₐ[E] K)) (NumberField.SIdele.diag E K S) 2).hom
        (H2π (SUnits.sUnitsRep E K S) f)) = H2π _ F := by
    rw [coindIso_hom_eq_map_subtype_comp_map_eval_one _ 2 ev hev]
    simp only [F, ModuleCat.hom_comp, LinearMap.comp_apply, H2π_comp_map_apply]
    rfl
  rw [hcoord]

  have hF : ∀ a b : FiniteSIdele.D E K v.1, F (a, b) =
      Additive.ofMul (Units.map (SUnits.loc E K v.1).toMonoidHom
        (SUnits.val E K S (f ((a : K ≃ₐ[E] K), (b : K ≃ₐ[E] K))))) := by
    intro a b
    change ((SUnits.diagIn E K S v).hom (f ((a : K ≃ₐ[E] K), (b : K ≃ₐ[E] K)))).1 1 = _
    rw [SUnits.diagIn_hom_apply_apply, one_smul]

  refine PlaceDecomp.H2π_eq_zero_of_exists_coboundary_above E K K'' w'' _ hw'' F y ?_
  intro g h a b ha hb
  rw [← hy g h, hF, ha, hb, toMul_ofMul]
  congr 1
  ext1
  simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, SUnits.loc]
  exact (HeightOneSpectrum.Extension.adicCompletionSemialgHom_coe K K'' _ _)

end S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary
end P2MW
export P2MW.S_NumberField_SIdele_localCoordinate_map_diag_H2pi_eq_zero_of_exists_layer_coboundary (solution)
