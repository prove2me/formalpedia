-- Prove2me | solution 2 for NoHair.schwarzschild_unit_cartesian_ricci_zero
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T23:35:02.879032+00:00
-- url     : https://prove2.me/submissions/2c77b92d-2cd0-4604-8c16-4be096eeeef1

import Definitions.Def_NoHair_KerrNewmanEinstein_Base

open NoHair NoHair.KNE Set
open scoped BigOperators Topology
set_option backward.isDefEq.respectTransparency false
noncomputable section

private abbrev Mat := Matrix (Fin 4) (Fin 4) ℝ
private abbrev rv := ksRadius 0
private def u (z : E4) : ℝ := (rv z)⁻¹
private def tvec : Fin 4 → ℝ := ![1,0,0,0]
private def pmat : Mat := !![0,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1]
private def eta : Mat := !![-1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1]
private def pos (z:E4) : Fin 4 → ℝ := ![0,z 1,z 2,z 3]
private def n (z : E4) (i : Fin 4) : ℝ := pos z i * u z
private lemma four (i : Fin 4) : i=0 ∨ i=1 ∨ i=2 ∨ i=3 := by fin_cases i <;> decide
private lemma v0 {α : Type*} (a b c d : α) : ![a,b,c,d] (0 : Fin 4) = a := rfl
private lemma v1 {α : Type*} (a b c d : α) : ![a,b,c,d] (1 : Fin 4) = b := rfl
private lemma v2 {α : Type*} (a b c d : α) : ![a,b,c,d] (2 : Fin 4) = c := rfl
private lemma v3 {α : Type*} (a b c d : α) : ![a,b,c,d] (3 : Fin 4) = d := rfl

private lemma flat (i j : Fin 4) : minkowski i j = eta i j := by
  rcases four i with rfl | rfl | rfl | rfl <;> rcases four j with rfl | rfl | rfl | rfl <;> rfl
private lemma basis (i j : Fin 4) : coordBasis i j =
    (!![1,0,0,0;0,1,0,0;0,0,1,0;0,0,0,1] : Mat) i j := by
  rcases four i with rfl | rfl | rfl | rfl <;> rcases four j with rfl | rfl | rfl | rfl <;> rfl

private lemma radius_eq (x : E4) : rv x = spatialRadius x := by
  let p := x 1^2+x 2^2+x 3^2
  have hp : 0 ≤ p := by dsimp [p]; positivity
  change Real.sqrt ((p-0^2+Real.sqrt ((p-0^2)^2+4*0^2*x 3^2))/2)=Real.sqrt p
  simp only [zero_pow (by decide : 2 ≠ 0),mul_zero,zero_mul,add_zero,sub_zero,Real.sqrt_sq hp]
  congr 1; ring

private lemma radiusCP (p : E4) (hp : 0 < rv p) : HasCP rv p (n p) := by
  have rsq : rv p ^ 2 = p 1^2+p 2^2+p 3^2 := by rw [radius_eq, spatialRadius, Real.sq_sqrt (by positivity)]
  have qual : DifferentiableAt ℝ rv p := by
    have hpos : 0 < p 1^2+p 2^2+p 3^2 := by rw [← rsq]; positivity
    rw [show rv=spatialRadius from funext radius_eq]
    unfold spatialRadius
    fun_prop (disch := exact hpos.ne')
  refine ⟨qual,fun k => ?_⟩
  apply (hasDerivAt_ksRadius_line 0 p (coordBasis k) hp).congr_deriv
  rcases four k with rfl|rfl|rfl|rfl <;>
    simp only [basis,Matrix.of_apply,v0,v1,v2,v3,n,pos,u,rv,zero_pow (by decide : 2 ≠ 0),
      mul_zero,zero_mul,add_zero,sub_zero,mul_one,zero_add] <;> field_simp [hp.ne'] <;> ring

private structure Atom where
  val : E4 → ℝ
  d : E4 → Fin 4 → ℝ
  cp : ∀ z, 0 < rv z → HasCP val z (d z)

private def ac (c : ℝ) : Atom := ⟨fun _ => c, fun _ _ => 0, fun z _ => HasCP.cst c z⟩
private instance : Add Atom where
  add f g := ⟨fun z => f.val z+g.val z,fun z k => f.d z k+g.d z k,fun z h => (f.cp z h).add (g.cp z h)⟩
private instance : Sub Atom where
  sub f g := ⟨fun z => f.val z-g.val z,fun z k => f.d z k-g.d z k,fun z h => (f.cp z h).sub (g.cp z h)⟩
private instance : Mul Atom where
  mul f g := ⟨fun z => f.val z*g.val z,fun z k => f.d z k*g.val z+f.val z*g.d z k,
    fun z h => (f.cp z h).mul (g.cp z h)⟩

private def inverseRadius : Atom := ⟨u, fun z i => -(u z)^2*n z i, by
  intro z h
  have hu := (HasCP.cst 1 z).div (radiusCP z h) h.ne'
  have hu' : HasCP u z (fun k => (0*rv z-1*n z k)/(rv z)^2) := by
    have eq : u = fun w => 1/rv w := by funext w; simp [u, one_div]
    rw [eq]
    exact hu
  apply hu'.congr_d
  intro k; dsimp only [u]; field_simp [h.ne'] <;> ring⟩

private lemma cpPos (z:E4) (i : Fin 4) : HasCP (fun p => pos p i) z (fun j => pmat i j) := by
  rcases four i with rfl|rfl|rfl|rfl
  · apply (HasCP.cst 0 z).congr_d
    intro j; rcases four j with rfl|rfl|rfl|rfl <;> rfl
  all_goals
    apply (hasCP_coord z _).congr_d
    intro j
    rcases four j with rfl|rfl|rfl|rfl <;> rfl

private def normal (i : Fin 4) : Atom := ⟨fun z => n z i,
  fun z j => u z*(pmat i j-n z i*n z j),by
  intro z h
  apply ((cpPos z i).mul (inverseRadius.cp z h)).congr_d
  intro j
  change pmat i j*u z + pos z i*(-(u z)^2*n z j) = u z*(pmat i j-pos z i*u z*n z j)
  ring⟩

private lemma kronecker_null (p : E4) (h : 0 < rv p) (i : Fin 4) :
    ksNull 0 p i = tvec i+n p i := by
  rcases four i with rfl|rfl|rfl|rfl <;>
    simp only [ksNull_zero,ksNull_one,ksNull_two,ksNull_three,tvec,n,pos,u,rv,v0,v1,v2,v3,
      zero_mul,add_zero,zero_add,mul_zero,sub_zero,zero_pow (by decide : 2 ≠ 0)] <;>
    field_simp [h.ne'] <;> ring

private lemma normal_unit (p : E4) (h : 0 < rv p) : n p 1^2+n p 2^2+n p 3^2=1 := by
  have hh := ks_rel 0 p h
  simpa only [kronecker_null p h,tvec,v1,v2,v3,zero_add] using hh

private lemma prof (p:E4) (h:0<rv p) : ksProfile 1 0 0 p=2*u p := by
  unfold ksProfile u
  change rv p^2*(2*1*rv p-0^2)/(rv p^4+0^2*p 3^2)=_
  field_simp [h.ne'] <;> ring

private def metricF {α : Type*} [Add α] [Mul α] (two U η : α) (N T : Fin 4 → α) (i j : Fin 4) :=
  η+two*U*(T i+N i)*(T j+N j)
private def metricAtom (i j:Fin 4) := metricF (ac 2) inverseRadius (ac (eta i j)) normal (fun i=>ac (tvec i)) i j
private def inverseF (U:ℝ) (N:Fin 4→ℝ) (i j:Fin 4) :=
  eta i j-2*U*(N i-tvec i)*(N j-tvec j)

private lemma metricEq (p:E4) (h:0<rv p) (i j:Fin 4) :
    kerrNewmanMetric 1 0 0 p i j = (metricAtom i j).val p := by
  change minkowski i j+ksProfile 1 0 0 p*ksNull 0 p i*ksNull 0 p j =
    eta i j+2*u p*(tvec i+n p i)*(tvec j+n p j)
  rw [flat,prof p h,kronecker_null p h,kronecker_null p h]

private lemma inverseEq (p:E4) (h:0<rv p) (i j:Fin 4) :
    invMetric (kerrNewmanMetric 1 0 0) p i j = inverseF (u p) (n p) i j := by
  have hn := ks_null 0 p h
  have hg : kerrNewmanMetric 1 0 0 p = Matrix.of (fun i j => minkowski i j+ksProfile 1 0 0 p*ksNull 0 p i*ksNull 0 p j) := rfl
  unfold invMetric
  rw [hg, Matrix.inv_eq_right_inv (mul_inv_KS _ _ hn)]
  have raised (l : Fin 4) : ![-ksNull 0 p 0,ksNull 0 p 1,ksNull 0 p 2,ksNull 0 p 3] l =
      n p l-tvec l := by
    rcases four l with rfl|rfl|rfl|rfl <;>
      simp only [v0,v1,v2,v3,kronecker_null p h,tvec,n,pos] <;> ring
  simp only [Matrix.of_apply,inverseF,flat,prof p h,raised]

private def gammaF {α : Type*} [Add α] [Sub α] [Mul α] (two U : α) (N T : Fin 4 → α) (P : Fin 4 → Fin 4 → α)
    (i j k:Fin 4) : α :=
  let L := N i-T i
  let B := two*P j k-two*N j*N k-N j*(T k+N k)-N k*(T j+N j)
  U*U*(L*B+(N i-two*U*L)*(T j+N j)*(T k+N k))
private def gammaAtom (i j k:Fin 4) := gammaF (ac 2) inverseRadius normal (fun i=>ac (tvec i))
  (fun i j=>ac (pmat i j)) i j k
private abbrev gam (U:ℝ) (N:Fin 4→ℝ) := gammaF 2 U N tvec pmat

private structure Jt where
  val : ℝ
  d : ℝ
private instance : Add Jt where add f g := ⟨f.val+g.val,f.d+g.d⟩
private instance : Sub Jt where sub f g := ⟨f.val-g.val,f.d-g.d⟩
private instance : Mul Jt where mul f g := ⟨f.val*g.val,f.d*g.val+f.val*g.d⟩
private def cj (c:ℝ) : Jt := ⟨c,0⟩
private def uj (U:ℝ) (N:Fin 4→ℝ) (h:Fin 4) : Jt := ⟨U,-U^2*N h⟩
private def nj (U:ℝ) (N:Fin 4→ℝ) (h i:Fin 4) : Jt := ⟨N i,U*(pmat i h-N i*N h)⟩
private def dg (U:ℝ) (N:Fin 4→ℝ) (i j h:Fin 4) :=
  (metricF (cj 2) (uj U N h) (cj (eta i j)) (nj U N h) (fun i=>cj (tvec i)) i j).d
private def dgam (U:ℝ) (N:Fin 4→ℝ) (i j k h:Fin 4) :=
  (gammaF (cj 2) (uj U N h) (nj U N h) (fun i=>cj (tvec i)) (fun i j=>cj (pmat i j)) i j k).d
private def rawConnection (U:ℝ) (N:Fin 4→ℝ) (i j k:Fin 4) :=
  (1/2:ℝ)*∑ l, inverseF U N i l*(dg U N l k j+dg U N l j k-dg U N j k l)
private def rawRicci (U:ℝ) (N:Fin 4→ℝ) (s v:Fin 4) :=
  ∑ h, (dgam U N h v s h-dgam U N h h s v+
    ∑ l, (gam U N h h l*gam U N l v s-gam U N h v l*gam U N l h s))
private lemma jaV (a b:Jt) : (a+b).val = a.val+b.val := rfl
private lemma jaD (a b:Jt) : (a+b).d = a.d+b.d := rfl
private lemma jsV (a b:Jt) : (a-b).val = a.val-b.val := rfl
private lemma jsD (a b:Jt) : (a-b).d = a.d-b.d := rfl
private lemma jmV (a b:Jt) : (a*b).val = a.val*b.val := rfl
private lemma jmD (a b:Jt) : (a*b).d = a.d*b.val+a.val*b.d := rfl

private lemma perm_basics (σ : Equiv.Perm (Fin 4)) (hσ : σ 0=0) :
    (∀ i, tvec (σ i)=tvec i) ∧ (∀ i j, pmat (σ i) (σ j)=pmat i j) ∧
      (∀ i j, eta (σ i) (σ j)=eta i j) := by
  have t0 (i:Fin 4) : tvec i=if i=0 then 1 else 0 := by fin_cases i <;> rfl
  have p0 (i j:Fin 4) : pmat i j=if i=0 then 0 else if i=j then 1 else 0 := by fin_cases i <;> fin_cases j <;> rfl
  have e0 (i j:Fin 4) : eta i j=if i=j then (if i=0 then -1 else 1) else 0 := by fin_cases i <;> fin_cases j <;> rfl
  have z (i:Fin 4) : σ i=0 ↔ i=0 := by
    calc
      (σ i=0) ↔ σ i=σ 0 := by rw [hσ]
      _ ↔ i=0 := σ.injective.eq_iff
  exact ⟨fun i => by simp only [t0,z],fun i j => by simp only [p0,z,σ.injective.eq_iff],
    fun i j => by simp only [e0,z,σ.injective.eq_iff]⟩

private lemma perm_formula (σ : Equiv.Perm (Fin 4)) (hσ : σ 0=0) (U:ℝ) (N:Fin 4→ℝ) :
    (∀ i j k, gam U (N ∘ σ) i j k=gam U N (σ i) (σ j) (σ k)) ∧
    (∀ i j k, rawConnection U (N ∘ σ) i j k=rawConnection U N (σ i) (σ j) (σ k)) ∧
    (∀ i j, rawRicci U (N ∘ σ) i j=rawRicci U N (σ i) (σ j)) := by
  obtain ⟨ht,hp,he⟩ := perm_basics σ hσ
  have iv (i j : Fin 4) : inverseF U (N ∘ σ) i j=inverseF U N (σ i) (σ j) := by
    simp only [inverseF,Function.comp_apply,ht,he]
  have d (i j k:Fin 4) : dg U (N ∘ σ) i j k=dg U N (σ i) (σ j) (σ k) := by
    simp only [dg,metricF,uj,nj,Function.comp_apply,hp,he,ht]
  have g (i j k:Fin 4) : gam U (N ∘ σ) i j k=gam U N (σ i) (σ j) (σ k) := by
    simp only [gam,gammaF,Function.comp_apply,hp,ht]
  have dg' (i j k l:Fin 4) : dgam U (N ∘ σ) i j k l=dgam U N (σ i) (σ j) (σ k) (σ l) := by
    simp only [dgam,gammaF,uj,nj,Function.comp_apply,hp,he,ht]
  refine ⟨g,?_,?_⟩
  · intro i j k
    simp only [rawConnection,iv,d]
    congr 1
    exact Equiv.sum_comp σ (fun l => inverseF U N (σ i) l * (dg U N l (σ k) (σ j)+dg U N l (σ j) (σ k)-dg U N (σ j) (σ k) l))
  · intro i j
    simp only [rawRicci,dg',g]
    have inner (h:Fin 4) := Equiv.sum_comp σ
      (fun l => gam U N h h l * gam U N l (σ j) (σ i) - gam U N h (σ j) l * gam U N l h (σ i))
    simp only [inner]
    exact Equiv.sum_comp σ (fun h => dgam U N h (σ j) (σ i) h - dgam U N h h (σ i) (σ j) +
      ∑ l, (gam U N h h l*gam U N l (σ j) (σ i)-gam U N h (σ j) l*gam U N l h (σ i)))

private def sp132 : Equiv.Perm (Fin 4) where
  toFun := ![0,1,3,2]
  invFun := ![0,1,3,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp132_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp132)=![0,X,Z,Y] := by
  funext i
  fin_cases i <;> rfl
private def sp213 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,1,3]
  invFun := ![0,2,1,3]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp213_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp213)=![0,Y,X,Z] := by
  funext i
  fin_cases i <;> rfl
private def sp231 : Equiv.Perm (Fin 4) where
  toFun := ![0,2,3,1]
  invFun := ![0,3,1,2]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp231_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp231)=![0,Y,Z,X] := by
  funext i
  fin_cases i <;> rfl
private def sp312 : Equiv.Perm (Fin 4) where
  toFun := ![0,3,1,2]
  invFun := ![0,2,3,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp312_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp312)=![0,Z,X,Y] := by
  funext i
  fin_cases i <;> rfl
private def sp321 : Equiv.Perm (Fin 4) where
  toFun := ![0,3,2,1]
  invFun := ![0,3,2,1]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl
private lemma sp321_vec (X Y Z:ℝ) : ((![0,X,Y,Z] : Fin 4→ℝ) ∘ sp321)=![0,Z,Y,X] := by
  funext i
  fin_cases i <;> rfl
private lemma conn_sym (U:ℝ) (N:Fin 4 → ℝ) (i j k:Fin 4) : rawConnection U N i j k=rawConnection U N i k j := by
  have d (k j l: Fin 4) : dg U N j k l = dg U N k j l := by
    simp only [dg,metricF,jmV,jmD,jaV,jaD,cj,nj,uj]; ring
  dsimp only [rawConnection]
  congr 1
  apply Finset.sum_congr rfl; intro l _
  rw [d j k l, add_comm (dg U N l k j)]
private lemma gam_sym (U:ℝ) (N:Fin 4 → ℝ) (i j k:Fin 4) : gam U N i j k = gam U N i k j := by
  have e : pmat j k=pmat k j := by rcases four j with rfl|rfl|rfl|rfl <;> rcases four k with rfl|rfl|rfl|rfl <;> rfl
  dsimp only [gam,gammaF]; rw [e]; ring

set_option maxHeartbeats 1400000 in
private lemma conn_000 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 0 0=gam U ![0,X,Y,Z] 0 0 0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^3)*h

set_option maxHeartbeats 1400000 in
private lemma conn_001 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 0 1=gam U ![0,X,Y,Z] 0 0 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (0)*h

set_option maxHeartbeats 1400000 in
private lemma conn_011 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 1 1=gam U ![0,X,Y,Z] 0 1 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-2*U^3*(3*X^2 - 2))*h

set_option maxHeartbeats 1400000 in
private lemma conn_012 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 0 1 2=gam U ![0,X,Y,Z] 0 1 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-6*U^3*X*Y)*h

set_option maxHeartbeats 1400000 in
private lemma conn_100 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 0 0=gam U ![0,X,Y,Z] 1 0 0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-2*U^3*X)*h

set_option maxHeartbeats 1400000 in
private lemma conn_101 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 0 1=gam U ![0,X,Y,Z] 1 0 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (0)*h

set_option maxHeartbeats 1400000 in
private lemma conn_102 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 0 2=gam U ![0,X,Y,Z] 1 0 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (0)*h

set_option maxHeartbeats 1400000 in
private lemma conn_111 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 1 1=gam U ![0,X,Y,Z] 1 1 1 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^3*X*(3*X^2 - 2))*h

set_option maxHeartbeats 1400000 in
private lemma conn_112 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 1 2=gam U ![0,X,Y,Z] 1 1 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (6*U^3*X^2*Y)*h

set_option maxHeartbeats 1400000 in
private lemma conn_122 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 2 2=gam U ![0,X,Y,Z] 1 2 2 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^3*X*(3*Y^2 - 2))*h

set_option maxHeartbeats 1400000 in
private lemma conn_123 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawConnection U ![0,X,Y,Z] 1 2 3=gam U ![0,X,Y,Z] 1 2 3 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (6*U^3*X*Y*Z)*h

private lemma conn_cert (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) (i j k:Fin 4) :
    rawConnection U ![0,X,Y,Z] i j k=gam U ![0,X,Y,Z] i j k := by
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl <;> rcases four k with rfl|rfl|rfl|rfl
  · exact conn_000 U X Y Z h
  · exact conn_001 U X Y Z h
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_001 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_001 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    exact conn_001 U X Y Z h
  · exact conn_011 U X Y Z h
  · exact conn_012 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_012 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_001 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_012 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_011 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 0 1 1).symm.trans (z.trans (H.1 0 1 1))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_012 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_001 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 0 1).symm.trans (z.trans (H.1 0 0 1))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_012 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_012 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 0 1 2).symm.trans (z.trans (H.1 0 1 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_011 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 0 1 1).symm.trans (z.trans (H.1 0 1 1))
  · exact conn_100 U X Y Z h
  · exact conn_101 U X Y Z h
  · exact conn_102 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_102 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    exact conn_101 U X Y Z h
  · exact conn_111 U X Y Z h
  · exact conn_112 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_112 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    exact conn_102 U X Y Z h
  · rw [conn_sym _ _ _ 2 1,gam_sym _ _ _ 2 1]
    exact conn_112 U X Y Z h
  · exact conn_122 U X Y Z h
  · exact conn_123 U X Y Z h
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_102 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · rw [conn_sym _ _ _ 3 1,gam_sym _ _ _ 3 1]
    have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_112 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_123 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := conn_122 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_100 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 0).symm.trans (z.trans (H.1 1 0 0))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_101 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_122 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · rw [conn_sym _ _ _ 1 2,gam_sym _ _ _ 1 2]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_123 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_101 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := conn_111 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.1 1 1 1).symm.trans (z.trans (H.1 1 1 1))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_102 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_123 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · rw [conn_sym _ _ _ 3 2,gam_sym _ _ _ 3 2]
    have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_112 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := conn_122 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_100 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 0).symm.trans (z.trans (H.1 1 0 0))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_101 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · rw [conn_sym _ _ _ 1 0,gam_sym _ _ _ 1 0]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_122 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_123 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · rw [conn_sym _ _ _ 1 3,gam_sym _ _ _ 1 3]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 2 0,gam_sym _ _ _ 2 0]
    have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_102 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 0 2).symm.trans (z.trans (H.1 1 0 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_123 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 2 3).symm.trans (z.trans (H.1 1 2 3))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_122 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 2 2).symm.trans (z.trans (H.1 1 2 2))
  · rw [conn_sym _ _ _ 2 3,gam_sym _ _ _ 2 3]
    have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · rw [conn_sym _ _ _ 3 0,gam_sym _ _ _ 3 0]
    have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_101 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 0 1).symm.trans (z.trans (H.1 1 0 1))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := conn_112 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.1 1 1 2).symm.trans (z.trans (H.1 1 1 2))
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := conn_111 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.1 1 1 1).symm.trans (z.trans (H.1 1 1 1))
set_option maxHeartbeats 1400000 in
private lemma ric_00 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 0 0=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (U^3*(4*U^2*X^2 + 4*U^2*Y^2 + 4*U^2*Z^2 - 3*U*X^2 - 3*U*Y^2 - 3*U*Z^2 + 6*U - 3))*h

set_option maxHeartbeats 1400000 in
private lemma ric_01 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 0 1=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (4*U^4*X*(U - 1))*h

set_option maxHeartbeats 1400000 in
private lemma ric_10 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 1 0=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (2*U^4*X*(2*U + 3))*h

set_option maxHeartbeats 1400000 in
private lemma ric_11 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 1 1=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (-U^3*(4*U^2*Y^2 + 4*U^2*Z^2 - 4*U^2 + 3*U*X^2 + 6*U*Y^2 + 6*U*Z^2 - 2*U + 3))*h

set_option maxHeartbeats 1400000 in
private lemma ric_12 (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) :
    rawRicci U ![0,X,Y,Z] 1 2=0 := by
  simp only [rawConnection, rawRicci, Fin.sum_univ_four, inverseF, dg, dgam, gam,
    gammaF,metricF,jaV,jaD,jsV,jsD,jmV,jmD,cj,uj,nj,tvec,pmat,eta,Matrix.of_apply,v0,v1,v2,v3,
    add_zero,zero_add,mul_zero,zero_mul,mul_one,one_mul,sub_zero,zero_sub] <;>
    linear_combination (U^4*X*Y*(4*U + 3))*h

private lemma ric_cert (U X Y Z:ℝ) (h:X^2+Y^2+Z^2=1) (i j:Fin 4) :
    rawRicci U ![0,X,Y,Z] i j=0 := by
  rcases four i with rfl|rfl|rfl|rfl <;> rcases four j with rfl|rfl|rfl|rfl
  · exact ric_00 U X Y Z h
  · exact ric_01 U X Y Z h
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_01 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 0 1).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_01 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 0 1).symm.trans z
  · exact ric_10 U X Y Z h
  · exact ric_11 U X Y Z h
  · exact ric_12 U X Y Z h
  · have H := perm_formula sp132 rfl U ![0,X,Y,Z]
    have z := ric_12 U X Z Y (by linarith only [h])
    rw [← sp132_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_10 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 1 0).symm.trans z
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_12 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp213 rfl U ![0,X,Y,Z]
    have z := ric_11 U Y X Z (by linarith only [h])
    rw [← sp213_vec X Y Z] at z
    exact (H.2.2 1 1).symm.trans z
  · have H := perm_formula sp231 rfl U ![0,X,Y,Z]
    have z := ric_12 U Y Z X (by linarith only [h])
    rw [← sp231_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_10 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 1 0).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_12 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp321 rfl U ![0,X,Y,Z]
    have z := ric_12 U Z Y X (by linarith only [h])
    rw [← sp321_vec X Y Z] at z
    exact (H.2.2 1 2).symm.trans z
  · have H := perm_formula sp312 rfl U ![0,X,Y,Z]
    have z := ric_11 U Z X Y (by linarith only [h])
    rw [← sp312_vec X Y Z] at z
    exact (H.2.2 1 1).symm.trans z

private lemma norm_vec (p : E4) : n p = ![0,n p 1,n p 2,n p 3] := by
  funext i
  rcases four i with rfl|rfl|rfl|rfl
  · change 0*u p=0; ring
  all_goals rfl

private lemma metricPartial (p : E4) (hp : 0 < rv p) (i j k : Fin 4) :
    coordPartial (fun z => kerrNewmanMetric 1 0 0 z i j) k p = dg (u p) (n p) i j k := by
  have ev : ∀ᶠ z in 𝓝 p, 0 < rv z :=
    (isOpen_lt continuous_const (continuous_ksRadius 0)).mem_nhds hp
  have hg : (fun z => kerrNewmanMetric 1 0 0 z i j) =ᶠ[𝓝 p] (metricAtom i j).val :=
    ev.mono (fun z hz => metricEq z hz i j)
  unfold coordPartial
  rw [hg.fderiv_eq]
  exact ((metricAtom i j).cp p hp).eq k

private lemma connection (p : E4) (hp : 0 < rv p) (i j k:Fin 4) :
    christoffel (kerrNewmanMetric 1 0 0) p i j k = gam (u p) (n p) i j k := by
  calc
    _ = rawConnection (u p) (n p) i j k := by
      simp only [christoffel,rawConnection,inverseEq p hp,metricPartial p hp,Finset.mul_sum,mul_assoc]
    _ = _ := by
      have C := conn_cert (u p) _ _ _ (normal_unit p hp) i j k
      simpa only [← norm_vec p] using C

private lemma connPartial (p : E4) (hp : 0 < rv p) (i j k l : Fin 4) :
    coordPartial (fun z => christoffel (kerrNewmanMetric 1 0 0) z i j k) l p = dgam (u p) (n p) i j k l := by
  have ev : ∀ᶠ z in 𝓝 p, 0 < rv z :=
    (isOpen_lt continuous_const (continuous_ksRadius 0)).mem_nhds hp
  have hg : (fun z => christoffel (kerrNewmanMetric 1 0 0) z i j k) =ᶠ[𝓝 p] (gammaAtom i j k).val :=
    ev.mono (fun z hz => connection z hz i j k)
  unfold coordPartial
  rw [hg.fderiv_eq]
  exact ((gammaAtom i j k).cp p hp).eq l

theorem solution (p : E4) (hp : 0 < ksRadius 0 p) (i j : Fin 4) :
    ricci (kerrNewmanMetric 1 0 0) p i j=0 := by
  calc
    _ = rawRicci (u p) (n p) i j := by simp only [ricci,riemann,connPartial p hp,connection p hp,rawRicci]
    _ = _ := by
      have C := ric_cert (u p) _ _ _ (normal_unit p hp) i j
      simpa only [← norm_vec p] using C
