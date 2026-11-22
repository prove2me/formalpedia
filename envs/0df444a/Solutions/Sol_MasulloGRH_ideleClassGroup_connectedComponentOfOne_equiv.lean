-- Prove2me | solution 1 for MasulloGRH.ideleClassGroup_connectedComponentOfOne_equiv
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @emmgaml
-- created : 2026-11-22T19:16:32.867681+00:00
-- url     : https://prove2.me/submissions/7c7a2803-63b4-41c2-8c53-d46c41d76d28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_MasulloGRH_HeckeLFunction
import Theorems.Thm_MasulloGRH_idele_class_group_topology
import Theorems.Thm_MasulloGRH_s_idele_class_group_open_embedding
import Theorems.Thm_MasulloGRH_normOneIdeleClassGroup_connectedComponentOfOne_equiv

open NumberField

set_option autoImplicit false

namespace Sol_MasulloGRH_ideleClassGroup_connectedComponentOfOne_equiv

open MasulloGRH IsDedekindDomain

variable {F : Type*} [Field F] [NumberField F]

lemma fin_mul_apply (g h : IdeleGroup F) (v : HeightOneSpectrum (𝓞 F)) :
    ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v =
      (g : AdeleRing (𝓞 F) F).2 v * (h : AdeleRing (𝓞 F) F).2 v := rfl

lemma inf_mul_apply (g h : IdeleGroup F) (w : InfinitePlace F) :
    ((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w =
      (g : AdeleRing (𝓞 F) F).1 w * (h : AdeleRing (𝓞 F) F).1 w := rfl

lemma fin_one_apply (v : HeightOneSpectrum (𝓞 F)) :
    ((1 : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := rfl

lemma inf_one_apply (w : InfinitePlace F) :
    ((1 : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w = 1 := rfl

/-- The finite-part norms of an idele are `1` at almost all places. -/
lemma mulSupport_finite (g : IdeleGroup F) :
    (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖(g : AdeleRing (𝓞 F) F).2 v‖).Finite := by
  have hx := ((g : AdeleRing (𝓞 F) F).2).eventually
  have hy := (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2).eventually
  have hxy : ∀ v, (g : AdeleRing (𝓞 F) F).2 v *
      ((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v = 1 := by
    intro v
    rw [← fin_mul_apply, mul_inv_cancel, fin_one_apply]
  have hev : ∀ᶠ v in Filter.cofinite, ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
    filter_upwards [hx, hy] with v h1 h2
    have n1 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).2 h1
    have n2 : ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ ≤ 1 :=
      (Valued.toNormedField.norm_le_one_iff).2 h2
    have n3 : ‖(g : AdeleRing (𝓞 F) F).2 v‖ *
        ‖((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
      rw [← norm_mul, hxy v, norm_one]
    nlinarith [norm_nonneg ((g : AdeleRing (𝓞 F) F).2 v),
      norm_nonneg (((g⁻¹ : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v)]
  exact Filter.eventually_cofinite.1 hev

lemma ideleNorm_mul' (g h : IdeleGroup F) :
    ideleNorm (g * h) = ideleNorm g * ideleNorm h := by
  unfold ideleNorm
  have e1 : ∀ w : InfinitePlace F,
      ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult =
        ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult * ‖(h : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult := by
    intro w
    rw [inf_mul_apply, norm_mul, mul_pow]
  have e2 : ∀ v : HeightOneSpectrum (𝓞 F),
      ‖((g * h : IdeleGroup F) : AdeleRing (𝓞 F) F).2 v‖ =
        ‖(g : AdeleRing (𝓞 F) F).2 v‖ * ‖(h : AdeleRing (𝓞 F) F).2 v‖ := by
    intro v
    rw [fin_mul_apply, norm_mul]
  simp_rw [e1, e2, Finset.prod_mul_distrib]
  rw [finprod_mul_distrib (mulSupport_finite g) (mulSupport_finite h)]
  ring

lemma ideleNorm_one' : ideleNorm (1 : IdeleGroup F) = 1 := by
  unfold ideleNorm
  simp_rw [inf_one_apply, fin_one_apply, norm_one, one_pow, Finset.prod_const_one, finprod_one,
    one_mul]

/-- The idelic norm as a monoid homomorphism `GL₁(𝔸_F) → ℝ`. -/
noncomputable def normHom (F : Type*) [Field F] [NumberField F] : IdeleGroup F →* ℝ where
  toFun := ideleNorm
  map_one' := ideleNorm_one'
  map_mul' := ideleNorm_mul'

lemma normHom_apply (g : IdeleGroup F) : normHom F g = ideleNorm g := rfl

lemma finite_norm_eq_one_of_mem {g : IdeleGroup F}
    (hg : g ∈ sIntegralIdeles (∅ : Finset (HeightOneSpectrum (𝓞 F))))
    (v : HeightOneSpectrum (𝓞 F)) : ‖(g : AdeleRing (𝓞 F) F).2 v‖ = 1 := by
  have h := hg v (Finset.notMem_empty v)
  apply le_antisymm
  · exact (Valued.toNormedField.norm_le_one_iff).2 h.le
  · exact (Valued.toNormedField.one_le_norm_iff).2 h.ge

lemma continuous_ideleNorm : Continuous (ideleNorm : IdeleGroup F → ℝ) := by
  obtain ⟨U, hU, hUo, -⟩ := s_idele_class_group_open_embedding F ∅
  let f : IdeleGroup F → ℝ := fun g => ∏ w : InfinitePlace F, ‖(g : AdeleRing (𝓞 F) F).1 w‖ ^ w.mult
  have hf : Continuous f := by
    have h0 : Continuous (fun g : IdeleGroup F => (g : AdeleRing (𝓞 F) F).1) :=
      continuous_fst.comp (Units.continuous_val (M := AdeleRing (𝓞 F) F))
    have h1 : ∀ w : InfinitePlace F, Continuous (fun x : InfiniteAdeleRing F => x w) :=
      fun w => continuous_apply w
    refine continuous_finsetProd _ (fun w _ => ?_)
    exact (continuous_norm.comp ((h1 w).comp h0)).pow _
  have h1 : (1 : IdeleGroup F) ∈ (U : Set (IdeleGroup F)) := U.one_mem
  have heq : f =ᶠ[nhds (1 : IdeleGroup F)] (normHom F) := by
    filter_upwards [hUo.mem_nhds h1] with g hg
    rw [hU] at hg
    rw [normHom_apply]
    unfold ideleNorm
    have : (∏ᶠ v : HeightOneSpectrum (𝓞 F), ‖(g : AdeleRing (𝓞 F) F).2 v‖) = 1 := by
      rw [finprod_congr (finite_norm_eq_one_of_mem hg), finprod_one]
    rw [this, mul_one]
  have hc : ContinuousAt (normHom F) 1 := hf.continuousAt.congr heq
  exact continuous_of_continuousAt_one (normHom F) hc

lemma principal_le_ker : principalIdeles F ≤ (normHom F).ker := by
  rintro x ⟨ξ, rfl⟩
  rw [MonoidHom.mem_ker, normHom_apply]
  exact (idele_class_group_topology F).2.2.2.2.1 ξ

/-- The idelic norm on the idele class group. -/
noncomputable def classNorm (F : Type*) [Field F] [NumberField F] : IdeleClassGroup F →* ℝ :=
  QuotientGroup.lift (principalIdeles F) (normHom F) principal_le_ker

lemma classNorm_mk (g : IdeleGroup F) :
    classNorm F (QuotientGroup.mk g : IdeleClassGroup F) = ideleNorm g := rfl

lemma continuous_classNorm : Continuous (classNorm F) :=
  (QuotientGroup.isQuotientMap_mk _).continuous_iff.2 continuous_ideleNorm

lemma ideleNorm_nonneg' (g : IdeleGroup F) : 0 ≤ ideleNorm g :=
  mul_nonneg (Finset.prod_nonneg fun _ _ => pow_nonneg (norm_nonneg _) _)
    (finprod_nonneg fun _ => norm_nonneg _)

lemma classNorm_pos (x : IdeleClassGroup F) : 0 < classNorm F x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  rw [classNorm_mk]
  have h := ideleNorm_mul' g g⁻¹
  rw [mul_inv_cancel, ideleNorm_one'] at h
  rcases (ideleNorm_nonneg' g).lt_or_eq with h' | h'
  · exact h'
  · rw [← h', zero_mul] at h
    exact absurd h one_ne_zero

/-- `C_F ≅ ℝ × C_F¹` as topological groups (with `ℝ_{>0} ≅ ℝ` by the logarithm). -/
lemma exists_split (K : Subgroup (IdeleClassGroup F))
    (hK : ∀ x : IdeleClassGroup F,
      x ∈ K ↔ ∃ g : IdeleGroup F, (QuotientGroup.mk g : IdeleClassGroup F) = x ∧
        ideleNorm g = 1) :
    Nonempty (Multiplicative ℝ × K ≃ₜ* IdeleClassGroup F) := by
  obtain ⟨σ, hσc, hσm, hσn⟩ := (idele_class_group_topology F).2.2.2.2.2.2
  have hNσ : ∀ t : ℝ, 0 < t → classNorm F (σ t) = t := by
    intro t ht
    obtain ⟨g, hg, hgn⟩ := hσn t ht
    rw [← hg, classNorm_mk, hgn]
  have hKmem : ∀ x, x ∈ K ↔ classNorm F x = 1 := by
    intro x
    rw [hK]
    constructor
    · rintro ⟨g, rfl, hg⟩
      rw [classNorm_mk, hg]
    · intro hx
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨g, rfl, by rwa [classNorm_mk] at hx⟩
  let τ : ℝ → IdeleClassGroup F := fun a => σ (Real.exp a)
  have hτc : Continuous τ := hσc.comp_continuous Real.continuous_exp (fun a => Real.exp_pos a)
  have hτm : ∀ a b, τ (a + b) = τ a * τ b := fun a b => by
    simp only [τ, Real.exp_add]
    exact hσm _ _ (Real.exp_pos a) (Real.exp_pos b)
  have hNτ : ∀ a, classNorm F (τ a) = Real.exp a := fun a => hNσ _ (Real.exp_pos a)
  have hinvmem : ∀ x, (τ (Real.log (classNorm F x)))⁻¹ * x ∈ K := by
    intro x
    rw [hKmem, map_mul, map_inv, hNτ, Real.exp_log (classNorm_pos x),
      inv_mul_cancel₀ (classNorm_pos x).ne']
  have hlog : Continuous fun x : IdeleClassGroup F => Real.log (classNorm F x) :=
    Real.continuousOn_log.comp_continuous continuous_classNorm
      (fun x => (classNorm_pos x).ne')
  refine ⟨{ toFun := fun p => τ (Multiplicative.toAdd p.1) * (p.2 : IdeleClassGroup F),
            invFun := fun x => (Multiplicative.ofAdd (Real.log (classNorm F x)), ⟨_, hinvmem x⟩),
            left_inv := ?_, right_inv := ?_, map_mul' := ?_,
            continuous_toFun := ?_, continuous_invFun := ?_ }⟩
  · rintro ⟨a, k⟩
    have hk : classNorm F (k : IdeleClassGroup F) = 1 := (hKmem _).1 k.2
    have h1 : Real.log (classNorm F (τ (Multiplicative.toAdd a) * (k : IdeleClassGroup F))) =
        Multiplicative.toAdd a := by
      rw [map_mul, hNτ, hk, mul_one, Real.log_exp]
    refine Prod.ext ?_ (Subtype.ext ?_)
    · change Multiplicative.ofAdd _ = a
      rw [h1]
      rfl
    · change (τ (Real.log _))⁻¹ * _ = (k : IdeleClassGroup F)
      rw [h1, inv_mul_cancel_left]
  · intro x
    change τ (Real.log (classNorm F x)) * ((τ (Real.log (classNorm F x)))⁻¹ * x) = x
    rw [mul_inv_cancel_left]
  · rintro ⟨a, k⟩ ⟨b, l⟩
    change τ (Multiplicative.toAdd a + Multiplicative.toAdd b) *
        ((k : IdeleClassGroup F) * (l : IdeleClassGroup F)) =
      τ (Multiplicative.toAdd a) * (k : IdeleClassGroup F) *
        (τ (Multiplicative.toAdd b) * (l : IdeleClassGroup F))
    rw [hτm]
    exact mul_mul_mul_comm (τ (Multiplicative.toAdd a)) (τ (Multiplicative.toAdd b))
      (k : IdeleClassGroup F) (l : IdeleClassGroup F)
  · exact (hτc.comp (continuous_toAdd.comp continuous_fst)).mul
      (continuous_subtype_val.comp continuous_snd)
  · exact (continuous_ofAdd.comp hlog).prodMk
      (((hτc.comp hlog).inv.mul continuous_id).subtype_mk _)

/-- A topological group isomorphism restricts to an isomorphism of the identity components. -/
def ccEquiv {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] (e : G ≃ₜ* H) :
    Subgroup.connectedComponentOfOne G ≃ₜ* Subgroup.connectedComponentOfOne H where
  toFun x := ⟨e x, by
    have h := (map_continuous e).mapsTo_connectedComponent (1 : G)
      (show (x : G) ∈ connectedComponent (1 : G) from x.2)
    rwa [map_one] at h⟩
  invFun y := ⟨e.symm y, by
    have h := (map_continuous e.symm).mapsTo_connectedComponent (1 : H)
      (show (y : H) ∈ connectedComponent (1 : H) from y.2)
    rwa [map_one] at h⟩
  left_inv x := Subtype.ext (e.symm_apply_apply (x : G))
  right_inv y := Subtype.ext (e.apply_symm_apply (y : H))
  map_mul' x y := Subtype.ext (map_mul e (x : G) (y : G))
  continuous_toFun := ((map_continuous e).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((map_continuous e.symm).comp continuous_subtype_val).subtype_mk _

lemma mem_cc_prod_iff {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [ConnectedSpace G] (p : G × H) :
    p ∈ connectedComponent (1 : G × H) ↔ p.2 ∈ connectedComponent (1 : H) := by
  rw [show (1 : G × H) = ((1 : G), (1 : H)) from rfl, connectedComponent_prod,
    PreconnectedSpace.connectedComponent_eq_univ, Set.mem_prod]
  simp

/-- The identity component of `G × H` for a connected group `G`. -/
def ccProd {G H : Type*} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H]
    [IsTopologicalGroup G] [IsTopologicalGroup H] [ConnectedSpace G] :
    Subgroup.connectedComponentOfOne (G × H) ≃ₜ* G × Subgroup.connectedComponentOfOne H where
  toFun p := ((p : G × H).1, ⟨(p : G × H).2, (mem_cc_prod_iff (p : G × H)).1 p.2⟩)
  invFun q := ⟨(q.1, (q.2 : H)), (mem_cc_prod_iff (G := G) (q.1, (q.2 : H))).2 q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).prodMk
    ((continuous_snd.comp continuous_subtype_val).subtype_mk _)
  continuous_invFun := (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _

/-- Product of two topological group isomorphisms. -/
def prodCongr' {A B C D : Type*} [Mul A] [Mul B] [Mul C] [Mul D] [TopologicalSpace A]
    [TopologicalSpace B] [TopologicalSpace C] [TopologicalSpace D]
    (e₁ : A ≃ₜ* B) (e₂ : C ≃ₜ* D) : A × C ≃ₜ* B × D where
  toFun p := (e₁ p.1, e₂ p.2)
  invFun q := (e₁.symm q.1, e₂.symm q.2)
  left_inv p := by simp
  right_inv q := by simp
  map_mul' p q := Prod.ext (map_mul e₁ _ _) (map_mul e₂ _ _)
  continuous_toFun := ((map_continuous e₁).comp continuous_fst).prodMk
    ((map_continuous e₂).comp continuous_snd)
  continuous_invFun := ((map_continuous e₁.symm).comp continuous_fst).prodMk
    ((map_continuous e₂.symm).comp continuous_snd)

/-- `Multiplicative X × Multiplicative Y ≅ Multiplicative (X × Y)`. -/
def multProd {X Y : Type*} [AddGroup X] [AddGroup Y] [TopologicalSpace X] [TopologicalSpace Y] :
    Multiplicative X × Multiplicative Y ≃ₜ* Multiplicative (X × Y) where
  toFun p := Multiplicative.ofAdd (Multiplicative.toAdd p.1, Multiplicative.toAdd p.2)
  invFun q := (Multiplicative.ofAdd (Multiplicative.toAdd q).1,
    Multiplicative.ofAdd (Multiplicative.toAdd q).2)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_ofAdd.comp
    ((continuous_toAdd.comp continuous_fst).prodMk (continuous_toAdd.comp continuous_snd))
  continuous_invFun := (continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)).prodMk
    (continuous_ofAdd.comp (continuous_snd.comp continuous_toAdd))

end Sol_MasulloGRH_ideleClassGroup_connectedComponentOfOne_equiv

open MasulloGRH Sol_MasulloGRH_ideleClassGroup_connectedComponentOfOne_equiv in
theorem solution (F : Type*) [Field F] [NumberField F] :
    Nonempty (Subgroup.connectedComponentOfOne (IdeleClassGroup F) ≃ₜ*
      Multiplicative (ℝ × (Fin (InfinitePlace.nrComplexPlaces F) → UnitAddCircle) ×
        (Fin (InfinitePlace.nrRealPlaces F + InfinitePlace.nrComplexPlaces F - 1) →
          AdeleRing (𝓞 ℚ) ℚ ⧸ (algebraMap ℚ (AdeleRing (𝓞 ℚ) ℚ)).range.toAddSubgroup))) := by
  let K : Subgroup (IdeleClassGroup F) := (classNorm F).ker
  have hK : ∀ x : IdeleClassGroup F,
      x ∈ K ↔ ∃ g : IdeleGroup F, (QuotientGroup.mk g : IdeleClassGroup F) = x ∧
        ideleNorm g = 1 := by
    intro x
    rw [MonoidHom.mem_ker]
    constructor
    · intro hx
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨g, rfl, by rwa [classNorm_mk] at hx⟩
    · rintro ⟨g, rfl, hg⟩
      rw [classNorm_mk, hg]
  obtain ⟨c⟩ := normOneIdeleClassGroup_connectedComponentOfOne_equiv F K hK
  obtain ⟨Φ⟩ := exists_split K hK
  have : ConnectedSpace (Multiplicative ℝ) := inferInstanceAs (ConnectedSpace ℝ)
  exact ⟨(ccEquiv Φ.symm).trans
    (ccProd.trans ((prodCongr' (ContinuousMulEquiv.refl _) c).trans multProd))⟩
