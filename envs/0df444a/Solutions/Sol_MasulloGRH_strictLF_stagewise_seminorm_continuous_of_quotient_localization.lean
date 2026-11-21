-- Prove2me | solution 1 for MasulloGRH.strictLF_stagewise_seminorm_continuous_of_quotient_localization
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-21T00:15:48.309052+00:00
-- url     : https://prove2.me/submissions/ef7b2dcb-fc44-4df3-8946-88def78373dd

import Definitions.Def_MasulloGRH_LocallyConvex

open Set Filter Topology
open scoped Pointwise

open MasulloGRH

private theorem disk_mem_final {E : Type*} [AddCommGroup E] [Module ℂ E]
    [orig : TopologicalSpace E] [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (X : ℕ → Submodule ℂ E) (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (htop : ‹TopologicalSpace E› = sInf {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E _ t Subtype.val})
    (D : Set E) (hc : Convex ℝ D) (hb : Balanced ℂ D)
    (hd : ∀ n, (X n).subtype ⁻¹' D ∈ 𝓝 0) : D ∈ 𝓝 0 := by
  have ha : Absorbent ℝ D := by
    apply absorbent_iff_eventually_nhdsNE_zero.mpr
    intro x
    obtain ⟨n,hn⟩ := hexh x
    have : ContinuousSMul ℝ (X n) := IsScalarTower.continuousSMul ℂ
    have H : Absorbent ℝ ((X n).subtype ⁻¹' D) := absorbent_nhds_zero (hd n)
    exact H.eventually_nhdsNE_zero (⟨x,hn⟩ : X n)
  let g := gaugeSeminorm hb hc ha
  have hg : Continuous g := by
    let q : SeminormFamily ℂ E (ULift Unit) := fun _ => g
    have hcomp (n : ℕ) : Continuous (g.comp (X n).subtype) := by
      apply Seminorm.continuous' (r:=1)
      apply mem_of_superset (hd n)
      intro x hx
      exact (Seminorm.mem_closedBall_zero _).mpr (gauge_le_one_of_mem hx)
    have topX (n : ℕ) : IsTopologicalAddGroup (X n) := inferInstance
    let t := q.moduleFilterBasis.topology
    have hq : @WithSeminorms ℂ E _ _ _ _ q t := ⟨rfl⟩
    have hgT : @Continuous E ℝ t _ g := hq.continuous_seminorm (ULift.up ())
    apply continuous_le_dom _ hgT
    apply htop.le.trans
    apply sInf_le
    refine ⟨⟨ULift Unit,inferInstance,q,hq⟩,?_⟩
    intro n
    exact (@WithSeminorms.continuous_iff_continuous_comp ℂ ℂ (X n) E _ _ _ _ _ _ _
      (RingHom.id ℂ) _ q (@instTopologicalSpaceSubtype E (fun x => x ∈ X n) orig)
      (topX n) t hq (X n).subtype).mpr (fun _ => hcomp n)
  apply mem_of_superset ((Seminorm.continuous_iff (p:=g) zero_lt_one).mp hg)
  intro x hx
  exact setOfPred_gauge_lt_one_subset_self hc ha.zero_mem ha ((g.mem_ball_zero).mp hx)

private theorem shrink_sub {E : Type*} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    {S : Set E} (hS : S ∈ 𝓝 0) : ∃ T ∈ 𝓝 (0:E), ∀ a ∈ T, ∀ b ∈ T, a-b ∈ S := by
  obtain ⟨T,hT,hTT⟩ := exists_nhds_zero_half hS
  have hneg : (fun x:E => -x) ⁻¹' T ∈ 𝓝 0 := continuous_neg.tendsto' 0 0 neg_zero hT
  exact ⟨T ∩ ((fun x:E => -x) ⁻¹' T), inter_mem hT hneg,
    fun a ha b hb => (sub_eq_add_neg a b) ▸ hTT _ ha.1 _ hb.2⟩

theorem solution
    (E : Type*) [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (hE : IsHLCS E) (X : ℕ → Submodule ℂ E) (hmono : Monotone X)
    (hexh : ∀ x : E, ∃ n, x ∈ X n)
    (htop : ‹TopologicalSpace E› = sInf {t | IsLocallyConvexTopology E t ∧
      ∀ n, @Continuous (X n) E _ t Subtype.val})
    (V : Submodule ℂ E)
    (hloc : ∀ n : ℕ, ∃ m : ℕ, n ≤ m ∧ ∃ U ∈ 𝓝 (0 : X n), ∀ W ∈ 𝓝 (0 : X m),
      ∃ G ∈ 𝓝 (0 : E ⧸ V), ∀ x ∈ U, Submodule.Quotient.mk (x : E) ∈ G →
        ∃ w ∈ W, ((x:E) - (w:E)) ∈ V)
    (p : Seminorm ℂ V)
    (hp : ∀ n, Continuous (p.comp (Submodule.inclusion (inf_le_left : V ⊓ X n ≤ V)))) :
    Continuous p := by
  classical
  obtain ⟨ι,hι,f,hf⟩ := hE.1
  have hadd := hf.topologicalAddGroup
  have hsm := hf.continuousSMul
  let q := V.mkQ
  have small (n : ℕ) (e : ℝ) (he : 0 < e) :
      ∃ T ∈ 𝓝 (0:E), ∀ a ∈ T, ∀ b ∈ T, ∀ c ∈ T, ∀ h : a+b-c ∈ V,
        a+b-c ∈ X n → p ⟨a+b-c,h⟩ ≤ e := by
    let i : ↥(V ⊓ X n) →ₗ[ℂ] V := Submodule.inclusion inf_le_left
    have hball : (p.comp i).ball 0 e ∈ 𝓝 0 := (Seminorm.continuous_iff he).mp (hp n)
    rw [nhds_subtype] at hball
    obtain ⟨G,hG,hGB⟩ := Filter.mem_comap.mp hball
    obtain ⟨K,hK,hKG⟩ := shrink_sub hG
    obtain ⟨T,hT,hTK⟩ := exists_nhds_zero_half hK
    refine ⟨T ∩ K,inter_mem hT hK,?_⟩
    intro a ha b hb c hc h hn
    exact ((p.comp i).mem_ball_zero.mp (hGB (a:=⟨a+b-c,h,hn⟩)
      (hKG _ (hTK _ ha.1 _ hb.1) _ hc.2))).le
  let budget (i : ℕ) : ℝ := 1 - (1/2:ℝ)^i
  let Ctrl (i : ℕ) (A : Set E) : Prop := ∃ m : ℕ, ∀ W ∈ 𝓝 (0 : X m),
    ∃ G ∈ 𝓝 (0 : E ⧸ V), ∀ x ∈ A, q x ∈ G →
      ∃ (v : V) (w : X m), w ∈ W ∧ x = (v:E) + w ∧ p v ≤ budget i
  let Good (i : ℕ) (A : Set E) := (0:E) ∈ A ∧ Balanced ℂ A ∧ Convex ℝ A ∧ Ctrl i A
  have init : Good 0 {0} := by
    refine ⟨mem_singleton _,?_,convex_singleton _,0,?_⟩
    · apply balanced_iff_smul_mem.mpr
      rintro a ha x rfl
      simp
    · intro W hW
      refine ⟨univ,univ_mem,?_⟩
      rintro x rfl _
      exact ⟨0,0,mem_of_mem_nhds hW,by simp,by simp [budget]⟩
  have step (i : ℕ) (A : Set E) (hA : Good i A) :
      ∃ B : Set E, Good (i+1) B ∧ A ⊆ B ∧ (X i).subtype ⁻¹' B ∈ 𝓝 0 := by
    obtain ⟨hA0,hAb,hAc,m,hm⟩ := hA
    let t := max i m
    have hit : i ≤ t := le_max_left _ _
    have hmt : m ≤ t := le_max_right _ _
    obtain ⟨M,htM,U,hU,hUloc⟩ := hloc t
    let e := (1/2:ℝ)^(i+1)
    have he : 0 < e := by dsimp [e]; positivity
    obtain ⟨T,hT,hsmall⟩ := small M e he
    obtain ⟨K,hK,hKU⟩ := exists_nhds_zero_half hU
    let im : X m →ₗ[ℂ] X t := Submodule.inclusion (hmono hmt)
    let ii : X i →ₗ[ℂ] X t := Submodule.inclusion (hmono hit)
    have him : Continuous im := continuous_subtype_val.subtype_mk _
    have hii : Continuous ii := continuous_subtype_val.subtype_mk _
    let Wm := im ⁻¹' K ∩ (X m).subtype ⁻¹' T
    have hWm : Wm ∈ 𝓝 0 := inter_mem ((him.tendsto' 0 0 (map_zero im)) hK)
      ((continuous_subtype_val.tendsto' (0:X m) (0:E) rfl) hT)
    obtain ⟨G,hG,hprev⟩ := hm Wm hWm
    obtain ⟨H,hH,hHG⟩ := shrink_sub hG
    let O := (ii ⁻¹' K ∩ (X i).subtype ⁻¹' T) ∩ (fun x:X i => q (x:E)) ⁻¹' H
    have hO : O ∈ 𝓝 0 := inter_mem (inter_mem ((hii.tendsto' 0 0 (map_zero ii)) hK)
       ((continuous_subtype_val.tendsto' (0:X i) (0:E) rfl) hT))
       (((V.continuous_mkQ.comp continuous_subtype_val).tendsto' (0:X i) 0 (map_zero _)) hH)
    have hfi := (X i).subtype.withSeminorms_induced hf
    obtain ⟨s,r,hr,hD⟩ := (hfi.mem_nhds_iff 0 O).mp hO
    let d := s.sup (f.comp (X i).subtype)
    let D := d.ball 0 r
    let B := A + (X i).subtype '' D
    have hbD : Balanced ℂ ((X i).subtype '' D) := by
      apply balanced_iff_smul_mem.mpr
      rintro a ha x ⟨y,hy,rfl⟩
      exact ⟨a • y,(d.balanced_ball_zero r).smul_mem ha hy,rfl⟩
    have hcD : Convex ℝ ((X i).subtype '' D) :=
      (d.convex_ball 0 r).linear_image ((X i).subtype.restrictScalars ℝ)
    have hinc : A ⊆ B := by
      intro a ha
      exact ⟨a,ha,0,⟨0,d.mem_ball_self hr,rfl⟩,add_zero _⟩
    refine ⟨B,⟨hinc hA0,hAb.add hbD,hAc.add hcD,M,?_⟩,hinc,?_⟩
    · intro W hW
      let WM := W ∩ (X M).subtype ⁻¹' T
      have hWM : WM ∈ 𝓝 0 := inter_mem hW
        ((continuous_subtype_val.tendsto' (0:X M) (0:E) rfl) hT)
      obtain ⟨G',hG',hcorrect⟩ := hUloc WM hWM
      refine ⟨H ∩ G',inter_mem hH hG',?_⟩
      rintro _ ⟨a,ha,_,⟨b,hb,rfl⟩,rfl⟩ hab
      obtain ⟨⟨hbK,hbT⟩,hbH⟩ := hD hb
      have hqa : q a ∈ G := by
        have h := hHG _ hab.1 _ hbH
        change q (a+(b:E)) - q (b:E) ∈ G at h
        simpa only [map_add,add_sub_cancel_right] using h
      obtain ⟨v,w,hw,hav,hpV⟩ := hprev a ha hqa
      let z : X t := im w + ii b
      have hz : z ∈ U := hKU _ hw.1 _ hbK
      have heq : q (a+(b:E)) = q (z:E) := by
        change q (a+(b:E)) = q ((w:E)+b)
        have hv0 : q (v:E) = 0 := (Submodule.Quotient.mk_eq_zero V).mpr v.property
        simp only [hav,map_add,hv0,zero_add]
      have hzG : q (z:E) ∈ G' := heq ▸ (show q (a+(b:E)) ∈ G' from hab.2)
      obtain ⟨w',hw',hv'⟩ := hcorrect z hz hzG
      let v' : V := ⟨(z:E) - (w':E),hv'⟩
      have hzM : (z:E) ∈ X M := hmono htM z.property
      have hbound : p v' ≤ e :=
        hsmall _ hw.2 _ hbT _ hw'.2 hv' ((X M).sub_mem hzM w'.property)
      refine ⟨v+v',w',hw'.1,?_,?_⟩
      · change a + (b:E) = ((v:E) + (((w:E)+(b:E))-(w':E))) + (w':E)
        rw [hav]; abel
      · apply (map_add_le_add p v v').trans
        calc p v + p v' ≤ budget i + e := add_le_add hpV hbound
             _ = budget (i+1) := by simp only [budget,e,pow_succ]; ring
    · apply mem_of_superset (hfi.hasBasis_zero_ball.mem_of_mem (i:=(s,r)) hr)
      intro b hb
      exact ⟨0,hA0,(b:E),⟨b,hb,rfl⟩,zero_add _⟩
  let next (i : ℕ) (a : {A : Set E // Good i A}) : {B : Set E // Good (i+1) B} :=
    ⟨(step i a a.property).choose,(step i a a.property).choose_spec.1⟩
  let a : (i : ℕ) → {A : Set E // Good i A} :=
    @Nat.rec (fun i => {A : Set E // Good i A}) ⟨{0},init⟩ next
  let D (i : ℕ) : Set E := (a i).val
  have hs (i : ℕ) : D i ⊆ D (i+1) ∧ (X i).subtype ⁻¹' D (i+1) ∈ 𝓝 0 := by
    change (a i).val ⊆ (next i (a i)).val ∧ _
    exact (step i (a i).val (a i).property).choose_spec.2
  have hmon : Monotone D := monotone_nat_of_le_succ (fun i => (hs i).1)
  have hu : (⋃ i, D i) ∈ 𝓝 (0:E) := by
    apply disk_mem_final X hexh htop _
    · exact hmon.directed_le.convex_iUnion (fun i => (a i).property.2.2.1)
    · exact balanced_iUnion (fun i => (a i).property.2.1)
    · intro n
      exact mem_of_superset (hs n).2 (preimage_mono (subset_iUnion D (n+1)))
  apply Seminorm.continuous' (r:=2)
  have hvu : V.subtype ⁻¹' (⋃ i, D i) ∈ 𝓝 0 :=
    (continuous_subtype_val.tendsto' (0:V) (0:E) rfl) hu
  apply mem_of_superset hvu
  intro x hx
  obtain ⟨i,hi⟩ := mem_iUnion.mp hx
  obtain ⟨m,hm⟩ := (a i).property.2.2.2
  obtain ⟨T,hT,hsmall⟩ := small m 1 zero_lt_one
  have hW : (X m).subtype ⁻¹' T ∈ 𝓝 0 := (continuous_subtype_val.tendsto' (0:X m) (0:E) rfl) hT
  obtain ⟨G,hG,hrep⟩ := hm _ hW
  have hxq : q (x:E) = 0 := (Submodule.Quotient.mk_eq_zero V).mpr x.property
  obtain ⟨u,w,hw,he,hpu⟩ := hrep (x:E) hi (hxq.symm ▸ mem_of_mem_nhds hG)
  have hwe : (w:E) = (x:E) - u := by rw [he]; abel
  have hwv : (w:E) ∈ V := hwe ▸ V.sub_mem x.property u.property
  let v : V := ⟨w,hwv⟩
  have hpv : p v ≤ 1 := by
    have hv0 : (w:E)+0-0 ∈ V := by simpa using hwv
    have hwm : (w:E)+0-0 ∈ X m := by simpa using w.property
    simpa [v] using hsmall _ hw 0 (mem_of_mem_nhds hT) 0 (mem_of_mem_nhds hT) hv0 hwm
  have hev : x = u+v := Subtype.ext he
  apply p.mem_closedBall_zero.mpr
  rw [hev]
  apply (map_add_le_add p u v).trans
  have hb : budget i ≤ 1 := sub_le_self _ (by positivity)
  linarith

