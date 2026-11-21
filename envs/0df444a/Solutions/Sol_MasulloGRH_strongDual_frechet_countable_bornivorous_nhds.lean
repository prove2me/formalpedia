-- Prove2me | solution 1 for MasulloGRH.strongDual_frechet_countable_bornivorous_nhds
-- status  : ACCEPTED   (prove)
-- author  : @marozols
-- created : 2026-11-20T23:42:24.993285+00:00
-- url     : https://prove2.me/submissions/b3125c71-22a5-4701-9f75-25c1db1c9dfc

import Mathlib
import Theorems.Thm_MasulloGRH_weakStar_barrel_mem_nhds_strongDual
import Theorems.Thm_MasulloGRH_weakDual_polar_isCompact_of_nhds

open Set Filter Topology Bornology MasulloGRH
open scoped Pointwise

private def disk {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (A : Set E) (r : ℝ) : Set (WeakDual ℂ E) := {f | ∀ x ∈ A, ‖f x‖ ≤ r}

private theorem disk_props {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    (A : Set E) (r : ℝ) (hr : 0 ≤ r) :
    0 ∈ disk A r ∧ IsClosed (disk A r) ∧ Balanced ℂ (disk A r) ∧ Convex ℝ (disk A r) := by
  refine ⟨fun x _ => (show ‖(0:ℂ)‖ ≤ r by simpa), ?_, ?_, ?_⟩
  · simp only [disk, ofPred_forall]
    exact isClosed_biInter (fun x _ => isClosed_le (WeakDual.eval_continuous x).norm continuous_const)
  · apply balanced_iff_smul_mem.mpr
    intro c hc f hf x hx
    change ‖c * f x‖ ≤ r
    rw [norm_mul]
    exact (mul_le_mul_of_nonneg_right hc (norm_nonneg _)).trans (by simpa using hf x hx)
  · intro f hf g hg a b ha hb hab x hx
    change ‖a • f x + b • g x‖ ≤ r
    calc
      _ ≤ ‖a • f x‖ + ‖b • g x‖ := norm_add_le _ _
      _ = a * ‖f x‖ + b * ‖g x‖ := by rw [norm_smul,norm_smul,Real.norm_of_nonneg ha,Real.norm_of_nonneg hb]
      _ ≤ a*r+b*r := add_le_add (mul_le_mul_of_nonneg_left (hf x hx) ha) (mul_le_mul_of_nonneg_left (hg x hx) hb)
      _ = r := by rw [←add_mul,hab,one_mul]

private theorem compact_join {F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
    [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] {S T : Set F} (hS : IsCompact S)
    (hT : IsCompact T) : IsCompact (convexJoin ℝ S T) := by
  let f (v : ℝ × (F × F)) := (1-v.1) • v.2.1 + v.1 • v.2.2
  have hc : Continuous f := by dsimp [f]; fun_prop
  have he : convexJoin ℝ S T = f '' (Icc (0:ℝ) 1 ×ˢ (S ×ˢ T)) := by
    ext z
    rw [mem_convexJoin]
    constructor
    · rintro ⟨s,hs,t,ht,hz⟩
      rw [segment_eq_image] at hz
      obtain ⟨u,hu,rfl⟩ := hz
      exact ⟨(u,s,t),⟨hu,hs,ht⟩,rfl⟩
    · rintro ⟨⟨u,s,t⟩,⟨hu,hs,ht⟩,rfl⟩
      exact ⟨s,hs,t,ht,by rw [segment_eq_image]; exact ⟨u,hu,rfl⟩⟩
  rw [he]
  exact (isCompact_Icc.prod (hS.prod hT)).image hc

private theorem balanced_join {F : Type*} [AddCommGroup F] [Module ℝ F] [Module ℂ F]
    [SMulCommClass ℝ ℂ F] {S T : Set F} (hS : Balanced ℂ S) (hT : Balanced ℂ T) :
    Balanced ℂ (convexJoin ℝ S T) := by
  apply balanced_iff_smul_mem.mpr
  intro c hc z hz
  obtain ⟨s,hs,t,ht,a,b,ha,hb,hab,rfl⟩ := mem_convexJoin.mp hz
  refine mem_convexJoin.mpr ⟨c • s,hS.smul_mem hc hs,c • t,hT.smul_mem hc ht,a,b,ha,hb,hab,?_⟩
  rw [smul_add, smul_comm a c, smul_comm b c]

private theorem compact_disks {F : Type*} [AddCommGroup F] [Module ℝ F] [Module ℂ F]
    [SMulCommClass ℝ ℂ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
    (K : ℕ → Set F) (V : Set F) (hV : Convex ℝ V)
    (hK : ∀ n, 0 ∈ K n ∧ IsCompact (K n) ∧ Balanced ℂ (K n) ∧ Convex ℝ (K n) ∧ K n ⊆ V) :
    ∃ C : ℕ → Set F, Monotone C ∧ ∀ n, K n ⊆ C n ∧ 0 ∈ C n ∧ IsCompact (C n) ∧
      Balanced ℂ (C n) ∧ Convex ℝ (C n) ∧ C n ⊆ V := by
  let C : ℕ → Set F := Nat.rec (K 0) (fun n S => convexJoin ℝ S (K (n+1)))
  have hC (n : ℕ) : K n ⊆ C n ∧ 0 ∈ C n ∧ IsCompact (C n) ∧ Balanced ℂ (C n) ∧ Convex ℝ (C n) ∧ C n ⊆ V := by
    induction n with
    | zero => exact ⟨Subset.rfl,hK 0⟩
    | succ n ih =>
      obtain ⟨_, hz,hc,hb,hv,hsub⟩ := ih
      obtain ⟨kz,kc,kb,kv,ks⟩ := hK (n+1)
      have hi := subset_convexJoin_right (𝕜:=ℝ) (t:=K (n+1)) (nonempty_of_mem hz)
      refine ⟨hi,hi kz,compact_join hc kc,balanced_join hb kb,hv.convexJoin kv,?_⟩
      rintro z h
      obtain ⟨x,hx,y,hy,hz⟩ := mem_convexJoin.mp h
      exact hV.segment_subset (hsub hx) (ks hy) hz
  exact ⟨C,monotone_nat_of_le_succ (fun n => subset_convexJoin_left (nonempty_of_mem (hK (n+1)).1)),hC⟩


private theorem small_compact_disks {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E] (V : Set E) (hV : V ∈ 𝓝 (0:E))
    (U : Set (StrongDual ℂ E)) (hb : ∀ S : Set (StrongDual ℂ E), IsVonNBounded ℂ S → Absorbs ℂ U S) :
    ∃ δ : ℝ, 0 < δ ∧ IsCompact (disk V δ) ∧
      ∀ f ∈ disk V δ, (f : WeakDual ℂ E).toStrongDual + f.toStrongDual ∈ U := by
  let S := {f : StrongDual ℂ E | ∀ x ∈ V, ‖f x‖ ≤ 1}
  have hs : IsVonNBounded ℂ S := by
    rw [ContinuousLinearMap.isVonNBounded_iff]
    intro A hA
    obtain ⟨r, hr,h⟩ := (hA hV).exists_pos
    have hnorm : ‖(r:ℂ)‖ = r := by simp [Real.norm_of_nonneg hr.le]
    rw [NormedSpace.isVonNBounded_iff']
    refine ⟨r, ?_⟩
    rintro _ ⟨f,hf,x,hx,rfl⟩
    obtain ⟨y,hy,rfl⟩ := h (r:ℂ) hnorm.ge hx
    change ‖f ((r:ℂ) • y)‖ ≤ r
    rw [map_smul, norm_smul, hnorm]
    simpa using mul_le_mul_of_nonneg_left (hf _ hy) hr.le
  obtain ⟨r,_,h⟩ := (hb S hs).exists_pos
  let M := max r 1
  have hM : 1 ≤ M := le_max_right _ _
  have hMp : 0 < M := by linarith
  have hnorm : ‖(M:ℂ)‖ = M := by simp [Real.norm_of_nonneg hMp.le]
  have hc : (M:ℂ) ≠ 0 := by exact_mod_cast hMp.ne'
  let δ := 1/(2*M)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδ₁ : δ ≤ 1 := by dsimp [δ]; apply (div_le_iff₀ (by positivity)).mpr; linarith
  refine ⟨δ,hδ,(weakDual_polar_isCompact_of_nhds E V hV).of_isClosed_subset
    (disk_props V δ hδ.le).2.1 (fun f hf x hx => (hf x hx).trans hδ₁),?_⟩
  intro f hf
  let v := f.toStrongDual + f.toStrongDual
  have hv : (M:ℂ) • v ∈ S := by
    intro x hx
    change ‖(M:ℂ) * (f x + f x)‖ ≤ 1
    rw [norm_mul,hnorm]
    calc
      _ ≤ M * (δ+δ) := mul_le_mul_of_nonneg_left ((norm_add_le _ _).trans (add_le_add (hf x hx) (hf x hx))) hMp.le
      _ = 1 := by dsimp [δ]; field_simp; ring
  obtain ⟨w,hw,he⟩ := h (M:ℂ) (by rw [hnorm]; exact le_max_left _ _) hv
  change (M:ℂ) • w = (M:ℂ) • v at he
  have hwv : w = v := smul_right_injective (StrongDual ℂ E) hc he
  change v ∈ U
  rwa [← hwv]

private theorem strong_disk_inside {E : Type*} [AddCommGroup E] [Module ℂ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousSMul ℂ E]
    (U : Set (StrongDual ℂ E)) (hU : U ∈ 𝓝 0) :
    ∃ (A : Set E) (r : ℝ), 0 < r ∧
      (StrongDual.toWeakDual ⁻¹' disk A r ∈ 𝓝 (0 : StrongDual ℂ E)) ∧
      ∀ f ∈ disk A r, (f : WeakDual ℂ E).toStrongDual + f.toStrongDual ∈ U := by
  have hn : {f : StrongDual ℂ E | f+f ∈ U} ∈ 𝓝 0 := by
    have h : ContinuousAt (fun f : StrongDual ℂ E => f+f) 0 := (continuous_id.add continuous_id).continuousAt
    exact h.preimage_mem_nhds (by simpa using hU)
  obtain ⟨⟨A,W⟩,⟨hA,hW⟩,hsub⟩ := ContinuousLinearMap.hasBasis_nhds_zero.mem_iff.mp hn
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨A,r/2,by positivity,?_,?_⟩
  · apply mem_of_superset (ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem
      (i := (A, Metric.ball (0:ℂ) (r/2))) ⟨hA, Metric.ball_mem_nhds _ (by positivity)⟩)
    exact fun f hf x hx => (mem_ball_zero_iff.mp (hf x hx)).le
  · intro f hf
    exact hsub (a:=f.toStrongDual) (fun x hx => hball (mem_ball_zero_iff.mpr ((hf x hx).trans_lt (by linarith))))

theorem solution (E : Type*) [AddCommGroup E] [Module ℂ E]
    [TopologicalSpace E] (hE : IsFrechet E) (U : ℕ → Set (StrongDual ℂ E))
    (hU : ∀ n, U n ∈ nhds (0 : StrongDual ℂ E) ∧ IsClosed (U n) ∧
      Balanced ℂ (U n) ∧ Convex ℝ (U n))
    (hbor : ∀ S : Set (StrongDual ℂ E), IsVonNBounded ℂ S → Absorbs ℂ (⋂ n, U n) S) :
    (⋂ n, U n) ∈ nhds (0 : StrongDual ℂ E) := by
  classical
  have hlcs : IsHLCS E := ⟨hE.1,hE.2.1.1⟩
  obtain ⟨⟨ι,_,p,hp⟩,_,hmet⟩ := hE
  have hadd := hp.topologicalAddGroup
  have hsmul := hp.continuousSMul
  have hcomm : SMulCommClass ℝ ℂ (WeakDual ℂ E) :=
    ⟨fun a c f => by apply DFunLike.ext; intro x; exact smul_comm a c (f x)⟩
  have htower : IsScalarTower ℝ ℂ (WeakDual ℂ E) :=
    ⟨fun a c f => by apply DFunLike.ext; intro x; exact smul_assoc a c (f x)⟩
  have hcR : ContinuousSMul ℝ (WeakDual ℂ E) := IsScalarTower.continuousSMul ℂ
  obtain ⟨V,hV⟩ := (𝓝 (0:E)).exists_antitone_basis
  choose δ hδ hcompact hinside using fun n =>
    small_compact_disks (V n) (hV.mem n) (⋂ k, U k) hbor
  choose A r hr hstrong hD using fun n => strong_disk_inside (U n) (hU n).1
  let D (n:ℕ) := disk (A n) (r n)
  let K (n:ℕ) := disk (V n) (δ n)
  let J : WeakDual ℂ E →ₗ[ℝ] StrongDual ℂ E := {
    toFun := fun f => f.toStrongDual + f.toStrongDual
    map_add' := fun f g => by change (f.toStrongDual+g.toStrongDual)+(f.toStrongDual+g.toStrongDual) = _; abel
    map_smul' := fun a f => by change a • f.toStrongDual + a • f.toStrongDual = a • (f.toStrongDual + f.toStrongDual); rw [smul_add] }
  have hconv := (convex_iInter (fun n => (hU n).2.2.2)).linear_preimage J
  obtain ⟨C,hmono,hC⟩ := @compact_disks (WeakDual ℂ E) _ _ _ hcomm _ _ hcR K _ hconv (fun n => ⟨(disk_props _ _ (hδ n).le).1,
    hcompact n,(disk_props _ _ (hδ n).le).2.2.1,(disk_props _ _ (hδ n).le).2.2.2,hinside n⟩)
  let W := ⋂ n, C n + D n
  have hwclosed : IsClosed W := isClosed_iInter (fun n =>
    ((disk_props (A n) (r n) (hr n).le).2.1).add_left_of_isCompact (hC n).2.2.1)
  have hwbal : Balanced ℂ W := balanced_iInter (fun n =>
    (hC n).2.2.2.1.add (disk_props _ _ (hr n).le).2.2.1)
  have hwconv : Convex ℝ W := convex_iInter (fun n =>
    (hC n).2.2.2.2.1.add (disk_props _ _ (hr n).le).2.2.2)
  have hwabs : Absorbent ℂ W := by
    rw [absorbent_iff_inv_smul]
    intro f
    have hfV : {x : E | ‖f x‖ < 1} ∈ 𝓝 0 :=
      (isOpen_lt f.toStrongDual.continuous.norm continuous_const).mem_nhds (by simp)
    obtain ⟨k,hk⟩ := hV.mem_iff.mp hfV
    have hKevent : ∀ᶠ c : ℂ in cobounded ℂ, c⁻¹ • f ∈ K k := by
      have hinv : Tendsto (fun c : ℂ => ‖c⁻¹‖) (cobounded ℂ) (𝓝 0) := by
        simpa using (Filter.tendsto_inv₀_cobounded (α:=ℂ)).norm
      filter_upwards [hinv.eventually_lt_const (hδ k)] with c hc
      intro x hx
      change ‖c⁻¹ * f x‖ ≤ δ k
      rw [norm_mul]
      have hb : ‖f x‖ < 1 := hk hx
      exact (mul_le_of_le_one_right (norm_nonneg _) hb.le).trans hc.le
    have hEarly : ∀ᶠ c : ℂ in cobounded ℂ, ∀ i ∈ Finset.range k, c⁻¹ • f ∈ D i := by
      apply (eventually_all_finite (Finset.range k).finite_toSet).mpr
      intro i _
      exact (absorbent_iff_inv_smul.mp (absorbent_nhds_zero (𝕜:=ℂ) (hstrong i))) f.toStrongDual
    filter_upwards [hKevent,hEarly] with c hck hce
    apply mem_iInter.mpr
    intro n
    by_cases hkn : k ≤ n
    · have hmem := hmono hkn ((hC k).1 hck)
      exact ⟨_,hmem,0,(disk_props _ _ (hr n).le).1,add_zero _⟩
    · exact ⟨0,(hC n).2.1,_,hce n (Finset.mem_range.mpr (Nat.lt_of_not_ge hkn)),zero_add _⟩
  apply mem_of_superset (weakStar_barrel_mem_nhds_strongDual E hlcs W hwclosed hwbal hwconv hwabs)
  intro f hf
  apply mem_iInter.mpr
  intro n
  obtain ⟨b,hb,d,hd,he⟩ := mem_iInter.mp (show StrongDual.toWeakDual f ∈ W from hf) n
  have h1 := mem_iInter.mp ((hC n).2.2.2.2.2 hb) n
  have h2 := hD n d hd
  have hv : Convex ℝ (U n) := (hU n).2.2.2
  have hmid := hv h1 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  change b+d = StrongDual.toWeakDual f at he
  have he' : b.toStrongDual+d.toStrongDual = f := congrArg WeakDual.toStrongDual he
  convert hmid using 1
  rw [← he']
  change b.toStrongDual+d.toStrongDual = (1/2:ℝ) • (b.toStrongDual+b.toStrongDual) + (1/2:ℝ) • (d.toStrongDual+d.toStrongDual)
  module
